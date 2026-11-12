#include "LoweringExecution.hpp"
#include <codegen/x86/DepositExtractLowering.hpp>
#include <codegen/x86/IAmd64OnlyInstructionMatcher.hpp>
#include <codegen/CodegenException.hpp>
#include <array>
#include <cstring>
#include <functional>
#include <memory>
#include <optional>
#include <iostream>
#include <random>
#include <span>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

using LoweringExecution::Bytes;
using Codegen::DepositExtractOperation;

constexpr std::array kOperations{DepositExtractOperation::Deposit, DepositExtractOperation::Extract};

void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}

std::uint8_t prefix(DepositExtractOperation operation) {
    return operation == DepositExtractOperation::Deposit ? 3 : 2;
}

Bytes instruction(DepositExtractOperation operation, bool wide, std::uint8_t dst, std::uint8_t src, std::uint8_t mask) {
    return {0xC4, static_cast<std::uint8_t>(0xE2 ^ ((dst & 8) << 4) ^ ((mask & 8) << 2)),
        static_cast<std::uint8_t>((wide ? 0x80 : 0) | ((~src & 15) << 3) | prefix(operation)), 0xF5,
        static_cast<std::uint8_t>(0xC0 | ((dst & 7) << 3) | (mask & 7))};
}

Bytes memorySite(DepositExtractOperation operation, bool wide, const Bytes& tail) {
    Bytes site{0xC4, 0xE2, static_cast<std::uint8_t>((wide ? 0x80 : 0) | 0x40 | prefix(operation)), 0xF5};
    site.insert(site.end(), tail.begin(), tail.end());
    return site;
}

void decoding() {
    for (const auto operation : kOperations) {
        for (bool wide : {false, true}) {
            for (std::uint8_t dst = 0; dst < 16; ++dst) {
                for (std::uint8_t src = 0; src < 16; ++src) {
                    for (std::uint8_t mask = 0; mask < 16; ++mask) {
                        const auto bytes = instruction(operation, wide, dst, src, mask);
                        const auto operands = Codegen::DecodeDepositExtract(bytes.data(), bytes.size());
                        require(operands && operands->Operation == operation && operands->Wide == wide && operands->Destination == dst && operands->Source == src && operands->Mask == mask && !operands->Memory, "deposit/extract register decoding changed an operand");
                    }
                }
            }
        }
    }
    const Bytes memory{0x64, 0x67, 0xC4, 0x02, 0xAB, 0xF5, 0x8C, 0xAC, 0x10, 0, 0, 0};
    const auto operands = Codegen::DecodeDepositExtract(memory.data(), memory.size());
    require(operands && operands->Operation == DepositExtractOperation::Deposit && operands->Destination == 9 && operands->Source == 10 && operands->Memory && operands->Memory->RexIndexBase == 3 && operands->Memory->Prefixes == Bytes{0x64, 0x67}, "deposit/extract memory extensions or prefixes were lost");
    for (const Bytes bytes : {Bytes{0x90}, Bytes{0xC4, 0xE2, 0xF3}, Bytes{0xC4, 0xE1, 0xF3, 0xF5, 0xC0}, Bytes{0xC4, 0xE2, 0xF0, 0xF5, 0xC0}, Bytes{0xC4, 0xE2, 0xF1, 0xF5, 0xC0}, Bytes{0xC4, 0xE2, 0xF3, 0xF6, 0xC0}, Bytes{0xC4, 0xE2, 0xF2, 0xF7, 0xC0}, Bytes{0xC5, 0xF3, 0xF5, 0xC0, 0x90}})
        require(!Codegen::DecodeDepositExtract(bytes.data(), bytes.size()), "Unrelated, truncated, BZHI, MULX or SARX opcode matched PDEP or PEXT");
    for (const Bytes bytes : {Bytes{0xC4, 0xE2, 0xF7, 0xF5, 0xC0}, Bytes{0xC4, 0xE2, 0xF2, 0xF5, 0xC0, 0x90}, Bytes{0xC4, 0xE2, 0xF3, 0xF5, 0x84}}) {
        bool rejected = false;
        try { (void)Codegen::DecodeDepositExtract(bytes.data(), bytes.size()); }
        catch (const Codegen::CodegenException&) { rejected = true; }
        require(rejected, "Malformed deposit/extract instruction was accepted");
    }
    const Bytes overflow{0xC4, 0xE2, 0xF3, 0xF5, 0x84, 0x24, 0xFF, 0xFF, 0xFF, 0x7F};
    bool rejected = false;
    try {
        Codegen::StubBodyBuilder body;
        Codegen::EmitDepositExtract(body, *Codegen::DecodeDepositExtract(overflow.data(), overflow.size()));
    } catch (const Codegen::CodegenException&) { rejected = true; }
    require(rejected, "An overflowing stack displacement was silently wrapped");
}

void matching() {
    const auto intel = Codegen::MakeAmd64OnlyInstructionMatcher();
    const auto rosetta = Codegen::MakeAmd64OnlyInstructionMatcher(Codegen::Amd64OnlyTarget::Rosetta);
    for (const auto operation : kOperations) {
        const auto bytes = instruction(operation, true, 0, 2, 6);
        const auto name = Codegen::DepositExtractName(operation);
        require(!intel->Match(bytes.data(), bytes.size()), std::string("Intel mode rewrote ") + name);
        const auto match = rosetta->Match(bytes.data(), bytes.size());
        require(match && match->InstructionName == name && match->Lowering == Codegen::Amd64OnlyLowering::Trampoline && !match->Optional, std::string("Rosetta mode did not require a trampoline for ") + name);
        const std::array<std::span<const std::uint8_t>, 2> sequence{bytes, bytes};
        require(rosetta->MatchSequence(sequence, {}).has_value(), std::string("A sequence could not move out of line for ") + name);
    }
}

#if LOWERING_EXECUTION_AVAILABLE

using LoweringExecution::Execution;
using LoweringExecution::State;

std::uint64_t model(DepositExtractOperation operation, bool wide, std::uint64_t source, std::uint64_t mask) {
    const unsigned bits = wide ? 64 : 32;
    std::uint64_t result = 0;
    unsigned k = 0;
    for (unsigned m = 0; m < bits; ++m) {
        if (((mask >> m) & 1) == 0) continue;
        if (operation == DepositExtractOperation::Deposit)
            result |= ((source >> k) & 1) << m;
        else
            result |= ((source >> m) & 1) << k;
        ++k;
    }
    return result;
}

bool hostHasBmi2() {
    return LoweringExecution::HostExecutes({0xC4, 0xE2, 0xFB, 0xF5, 0xC0}) && LoweringExecution::HostExecutes({0xC4, 0xE2, 0xFA, 0xF5, 0xC0});
}

using Prelude = std::function<void(Codegen::StubBodyBuilder&)>;

std::vector<std::unique_ptr<Execution>> executables(const Bytes& site, std::uint64_t memoryValue, bool native, const Prelude& prelude = {}) {
    const auto operands = Codegen::DecodeDepositExtract(site.data(), site.size());
    require(operands.has_value(), "Execution site was not PDEP or PEXT");
    const bool rip = operands->Memory && operands->Memory->RipRelative;
    std::vector<std::unique_ptr<Execution>> executions;
    executions.push_back(std::make_unique<Execution>(site, memoryValue, rip, [&](Codegen::StubBodyBuilder& body, const Bytes& relocated) {
        if (prelude) prelude(body);
        Codegen::EmitDepositExtract(body, *Codegen::DecodeDepositExtract(relocated.data(), relocated.size()));
    }));
    if (native)
        executions.push_back(std::make_unique<Execution>(site, memoryValue, rip, [&](Codegen::StubBodyBuilder& body, const Bytes& relocated) {
            if (prelude) prelude(body);
            body.Raw(relocated);
        }));
    return executions;
}

std::string describe(const Codegen::DepositExtractOperands& operands, bool native, std::uint64_t source, std::uint64_t mask) {
    return std::string(native ? "host " : "stub ") + Codegen::DepositExtractName(operands.Operation) + (operands.Wide ? " 64" : " 32") + " dst " + std::to_string(operands.Destination) + " src " + std::to_string(operands.Source) + " mask " + std::to_string(operands.Mask) + (operands.Memory ? " memory" : "") + " (source " + std::to_string(source) + ", mask value " + std::to_string(mask) + ")";
}

void check(const State& state, const Codegen::DepositExtractOperands& operands, bool native, std::uint64_t source, std::uint64_t mask) {
    const auto wanted = model(operands.Operation, operands.Wide, source, mask);
    for (std::size_t reg = 0; reg < 16; ++reg) {
        const auto value = reg == operands.Destination ? wanted : state.Input[reg];
        if (state.Output[reg] != value)
            throw std::runtime_error(describe(operands, native, source, mask) + ": register " + std::to_string(reg) + " is " + std::to_string(state.Output[reg]) + ", wanted " + std::to_string(value));
    }
    if ((state.Flags & LoweringExecution::kFlagMask) != (state.InputFlags & LoweringExecution::kFlagMask))
        throw std::runtime_error(describe(operands, native, source, mask) + ": flags changed to " + std::to_string(state.Flags & LoweringExecution::kFlagMask));
    for (const auto value : state.RedZone) require(value == LoweringExecution::kSentinel, describe(operands, native, source, mask) + ": the caller's red zone was overwritten");
}

using Setup = std::function<void(State&, const Execution&)>;

void run(const std::vector<std::unique_ptr<Execution>>& executions, const Codegen::DepositExtractOperands& operands, const State& initial, std::optional<std::uint64_t> memoryValue, const Setup& setup = {}) {
    for (std::size_t index = 0; index < executions.size(); ++index) {
        auto state = initial;
        if (setup) setup(state, *executions[index]);
        for (const auto flags : {LoweringExecution::kBaseFlags | LoweringExecution::kFlagMask, LoweringExecution::kBaseFlags}) {
            state.InputFlags = flags;
            auto trial = state;
            executions[index]->Run(trial);
            const auto mask = memoryValue ? *memoryValue : trial.Input[operands.Mask];
            check(trial, operands, index != 0, trial.Input[operands.Source], mask);
        }
    }
}

void execution() {
    const bool native = hostHasBmi2();
    std::cout << (native ? "checking the stub and the host PDEP and PEXT against the SDM model\n" : "the host lacks PDEP or PEXT; checking the stub against the SDM model only\n");
    constexpr std::array<std::uint64_t, 7> sources{0, 1, 0x80000000ull, 0x8000000000000000ull, 0xFFFFFFFFFFFFFFFFull, 0xABCD123456789000ull, 0x5555AAAA3333CCCCull};
    constexpr std::array<std::uint64_t, 10> masks{0, 1, 0x80000000ull, 0x8000000000000000ull, 0xFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull, 0xFF00FF00FF00FF00ull, 0x0123456789ABCDEFull, 0x00000001FFFFFFFEull, 0xAAAAAAAAAAAAAAAAull};
    for (const auto operation : kOperations) {
        for (bool wide : {false, true}) {
            for (std::uint8_t dst = 0; dst < 16; ++dst) {
                for (const auto regs : std::array<std::pair<std::uint8_t, std::uint8_t>, 10>{{{2, 6}, {dst, 10}, {11, dst}, {dst, dst}, {4, 9}, {9, 4}, {0, 1}, {1, 0}, {13, 13}, {8, 15}}}) {
                    const auto site = instruction(operation, wide, dst, regs.first, regs.second);
                    const auto operands = *Codegen::DecodeDepositExtract(site.data(), site.size());
                    const auto executions = executables(site, 0, native);
                    for (const auto source : sources) {
                        for (const auto mask : masks) {
                            auto state = LoweringExecution::InitialState();
                            state.Input[regs.first] = source;
                            state.Input[regs.second] = mask;
                            run(executions, operands, state, std::nullopt);
                        }
                    }
                }
            }
        }
    }
    std::mt19937_64 random(0x5EED);
    for (const auto operation : kOperations) {
        for (bool wide : {false, true}) {
            const auto site = instruction(operation, wide, 3, 12, 7);
            const auto operands = *Codegen::DecodeDepositExtract(site.data(), site.size());
            const auto executions = executables(site, 0, native);
            for (int trial = 0; trial < 25000; ++trial) {
                auto state = LoweringExecution::InitialState();
                state.Input[12] = random();
                state.Input[7] = (trial & 1) ? random() : random() & random();
                run(executions, operands, state, std::nullopt);
            }
        }
    }
    for (const auto operation : kOperations) {
        for (bool wide : {false, true}) {
            for (const Bytes tail : {Bytes{0x06}, Bytes{0x46, 0x10}, Bytes{0x84, 0x24, 0x40, 0, 0, 0}, Bytes{0x04, 0xCA}, Bytes{0x85, 0x10, 0, 0, 0}, Bytes{0x05, 0, 0, 0, 0}}) {
                for (const auto value : std::array<std::uint64_t, 3>{0, 0xFEDCBA9876543210ull, 0xFFFFFFFF00000000ull}) {
                    for (const auto source : std::array<std::uint64_t, 3>{0, 0x0123456789ABCDEFull, 0xFFFFFFFFFFFFFFFFull}) {
                        const auto site = memorySite(operation, wide, tail);
                        const auto operands = *Codegen::DecodeDepositExtract(site.data(), site.size());
                        const auto executions = executables(site, value, native);
                        auto state = LoweringExecution::InitialState();
                        state.Input[1] = 3;
                        state.Input[7] = source;
                        state.Output[0] = value;
                        run(executions, operands, state, value, [&](State& prepared, const Execution& execution) {
                            const auto memory = reinterpret_cast<std::uint64_t>(execution.Memory());
                            prepared.Input[6] = memory - (tail[0] == 0x46 ? 16 : 0);
                            prepared.Input[2] = memory - 3 * 8;
                            prepared.Input[5] = memory - 16;
                        });
                    }
                }
            }
            for (const std::uint8_t dst : std::array<std::uint8_t, 2>{0, 4}) {
                for (const std::int32_t displacement : {-264, -256, -255, -248, -240, -200, -192, -191, -184, -176, -144, -137, -136}) {
                    Bytes tail{static_cast<std::uint8_t>(0x84 | (dst << 3)), 0x24};
                    for (unsigned s = 0; s < 32; s += 8)
                        tail.push_back(static_cast<std::uint8_t>(static_cast<std::uint32_t>(displacement) >> s));
                    constexpr std::uint64_t value = 0xFEDCBA9876543210ull;
                    const auto site = memorySite(operation, wide, tail);
                    const auto operands = *Codegen::DecodeDepositExtract(site.data(), site.size());
                    const auto executions = executables(site, value, native, [&](Codegen::StubBodyBuilder& body) {
                        for (int part = 0; part < 2; ++part) {
                            Bytes store{0xC7, 0x84, 0x24};
                            const auto slot = static_cast<std::uint32_t>(displacement + part * 4);
                            const auto word = static_cast<std::uint32_t>(value >> (part * 32));
                            for (unsigned s = 0; s < 32; s += 8) store.push_back(static_cast<std::uint8_t>(slot >> s));
                            for (unsigned s = 0; s < 32; s += 8) store.push_back(static_cast<std::uint8_t>(word >> s));
                            body.Raw(store);
                        }
                    });
                    auto state = LoweringExecution::InitialState();
                    state.Input[7] = 0x0123456789ABCDEFull;
                    run(executions, operands, state, value);
                }
            }
        }
    }
}
#else
void execution() { std::cout << "deposit/extract execution checks require a Linux/macOS x86-64 build\n"; }
#endif

}

int main() {
    try {
        decoding();
        matching();
        execution();
        std::cout << "deposit/extract lowering checks passed\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
