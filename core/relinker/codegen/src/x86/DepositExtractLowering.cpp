#include <codegen/x86/DepositExtractLowering.hpp>
#include <codegen/x86/ScalarLowering.hpp>

namespace Codegen {

using namespace ScalarLowering;

namespace {

constexpr std::int32_t kResultSlot = 8;
constexpr std::int32_t kMaskSlot = 16;
constexpr std::int32_t kSourceSlot = 24;
constexpr std::int32_t kBitSlot = 32;
constexpr std::int32_t kOutputSlot = 40;
constexpr std::int32_t kStackResultSlot = 48;
constexpr std::int32_t kSpillBytes = 56;
constexpr std::int32_t kFrame = FrameSize + 48;
constexpr std::uint8_t kPushFlags = 0x9C;
constexpr std::uint8_t kPopFlags = 0x9D;
constexpr std::uint8_t kJumpZero = 0x74;
constexpr std::uint8_t kJump = 0xEB;

struct Scratches {
    std::uint8_t Result;
    std::uint8_t Mask;
    std::uint8_t Source;
    std::uint8_t Bit;
    std::uint8_t Output;
};

void _append(std::vector<std::uint8_t>& bytes, const std::vector<std::uint8_t>& more) {
    bytes.insert(bytes.end(), more.begin(), more.end());
}

void _load(StubBodyBuilder& body, const bool wide, const std::uint8_t target, const std::uint8_t reg, const std::int32_t frame) {
    if (reg == Stack)
        StackSlot(body, 0x8D, true, target, frame);
    else
        Register(body, 0x8B, wide, target, reg);
}

std::vector<std::uint8_t> _loop(const DepositExtractOperands& operands, const Scratches& s) {
    const bool wide = operands.Wide;
    auto step = RegisterBytes(0x8B, wide, s.Bit, s.Mask);
    _append(step, RegisterBytes(0xF7, wide, 3, s.Bit));
    _append(step, RegisterBytes(0x21, wide, s.Mask, s.Bit));
    std::vector<std::uint8_t> take;
    std::vector<std::uint8_t> advance;
    if (operands.Operation == DepositExtractOperation::Deposit) {
        _append(step, RegisterBytes(0xF6, false, 0, s.Source));
        step.push_back(1);
        take = RegisterBytes(0x09, wide, s.Bit, s.Result);
        advance = RegisterBytes(0xD1, wide, 5, s.Source);
    } else {
        _append(step, RegisterBytes(0x85, wide, s.Bit, s.Source));
        take = RegisterBytes(0x09, wide, s.Output, s.Result);
        advance = RegisterBytes(0x01, wide, s.Output, s.Output);
    }
    _append(advance, RegisterBytes(0x31, wide, s.Bit, s.Mask));
    step.push_back(kJumpZero);
    step.push_back(static_cast<std::uint8_t>(take.size()));
    _append(step, take);
    _append(step, advance);
    auto loop = RegisterBytes(0x85, wide, s.Mask, s.Mask);
    loop.push_back(kJumpZero);
    loop.push_back(static_cast<std::uint8_t>(step.size() + 2));
    _append(loop, step);
    loop.push_back(kJump);
    loop.push_back(static_cast<std::uint8_t>(-static_cast<std::int32_t>(loop.size() + 1)));
    if (loop.size() > 127) throw CodegenException("deposit/extract loop exceeds a short branch");
    return loop;
}

}

const char* DepositExtractName(const DepositExtractOperation operation) {
    switch (operation) {
    case DepositExtractOperation::Deposit: return "PDEP";
    case DepositExtractOperation::Extract: return "PEXT";
    }
    throw CodegenException("unknown deposit/extract operation");
}

std::optional<DepositExtractOperands> DecodeDepositExtract(const std::uint8_t* data, const std::size_t length) {
    std::size_t vex = 0;
    while (vex < length && LegacyPrefix(data[vex])) ++vex;
    if (vex + 5 > length || data[vex] != 0xC4 || (data[vex + 1] & 0x1F) != 2 || data[vex + 3] != 0xF5) return std::nullopt;
    const auto pp = static_cast<std::uint8_t>(data[vex + 2] & 3);
    DepositExtractOperation operation;
    if (pp == 3)
        operation = DepositExtractOperation::Deposit;
    else if (pp == 2)
        operation = DepositExtractOperation::Extract;
    else
        return std::nullopt;
    const auto name = DepositExtractName(operation);
    if ((data[vex + 2] & 4) != 0) throw CodegenException(std::string(name) + " requires VEX.L=0");
    const auto extensions = static_cast<std::uint8_t>(~data[vex + 1]);
    const auto modrm = data[vex + 4];
    DepositExtractOperands operands{
        operation,
        static_cast<std::uint8_t>(((modrm >> 3) & 7) | ((extensions & 0x80) >> 4)),
        static_cast<std::uint8_t>((~data[vex + 2] >> 3) & 15),
        static_cast<std::uint8_t>((modrm & 7) | ((extensions & 0x20) >> 2)),
        (data[vex + 2] & 0x80) != 0, std::nullopt};
    std::size_t end = vex + 5;
    if ((modrm >> 6) != 3) {
        const auto rex = static_cast<std::uint8_t>(((extensions & 0x20) >> 5) | ((extensions & 0x40) >> 5));
        operands.Memory = DecodeMemoryOperand(data, length, vex + 4, rex, {data, data + vex});
        end = vex + 4 + operands.Memory->EncodedSize;
    }
    if (end != length) throw CodegenException(std::string(name) + " has trailing bytes");
    return operands;
}

void EmitDepositExtract(StubBodyBuilder& body, const DepositExtractOperands& operands) {
    const auto name = DepositExtractName(operands.Operation);
    const bool extract = operands.Operation == DepositExtractOperation::Extract;
    auto used = operands.Memory ? UsedRegisters({operands.Destination, operands.Source}, operands.Memory)
                                : UsedRegisters({operands.Destination, operands.Source, operands.Mask}, std::nullopt);
    Scratches s{};
    s.Result = Scratch(used, name);
    s.Mask = Scratch(used, name);
    s.Source = Scratch(used, name);
    s.Bit = Scratch(used, name);
    if (extract) s.Output = Scratch(used, name);
    const auto frame = SelectFrame(operands.Memory, operands.Wide, kFrame, kSpillBytes);
    StackSlot(body, 0x8D, true, Stack, 8 - frame);
    body.Raw(std::array{kPushFlags});
    StackSlot(body, 0x89, true, s.Result, kResultSlot);
    StackSlot(body, 0x89, true, s.Mask, kMaskSlot);
    StackSlot(body, 0x89, true, s.Source, kSourceSlot);
    StackSlot(body, 0x89, true, s.Bit, kBitSlot);
    if (extract) StackSlot(body, 0x89, true, s.Output, kOutputSlot);
    _load(body, operands.Wide, s.Source, operands.Source, frame);
    if (operands.Memory)
        Memory(body, 0x8B, operands.Wide, *operands.Memory, s.Mask, name, frame);
    else
        _load(body, operands.Wide, s.Mask, operands.Mask, frame);
    Register(body, 0x31, false, s.Result, s.Result);
    if (extract) {
        auto one = RegisterBytes(0xC7, true, 0, s.Output);
        Append32(one, 1);
        body.Raw(one);
    }
    body.Raw(_loop(operands, s));
    if (operands.Destination == Stack)
        StackSlot(body, 0x89, operands.Wide, s.Result, kStackResultSlot);
    else
        Register(body, 0x8B, operands.Wide, operands.Destination, s.Result);
    if (extract) StackSlot(body, 0x8B, true, s.Output, kOutputSlot);
    StackSlot(body, 0x8B, true, s.Bit, kBitSlot);
    StackSlot(body, 0x8B, true, s.Source, kSourceSlot);
    StackSlot(body, 0x8B, true, s.Mask, kMaskSlot);
    StackSlot(body, 0x8B, true, s.Result, kResultSlot);
    body.Raw(std::array{kPopFlags});
    if (operands.Destination == Stack)
        StackSlot(body, 0x8B, operands.Wide, Stack, kStackResultSlot - 8);
    else
        StackSlot(body, 0x8D, true, Stack, frame - 8);
}

}
