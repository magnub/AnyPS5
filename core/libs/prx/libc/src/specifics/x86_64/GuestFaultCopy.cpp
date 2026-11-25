#if (defined(__linux__) || defined(__APPLE__)) && defined(__x86_64__)
#include "prx/libc/include/specifics/x86_64/GuestFaultCopy.hpp"

#include <atomic>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#ifdef __APPLE__
#include <pthread.h>
#include <sys/ucontext.h>
#define GUEST_FAULT_COPY_SYMBOL(name) "_" #name
#define GUEST_FAULT_COPY_LABEL(name) ".globl _" #name "\n.private_extern _" #name "\n.alt_entry _" #name "\n_" #name ":\n"
#define GUEST_FAULT_COPY_LOCAL(name) "L" #name
#else
#include <sys/syscall.h>
#include <ucontext.h>
#include <unistd.h>
#define GUEST_FAULT_COPY_SYMBOL(name) #name
#define GUEST_FAULT_COPY_LABEL(name) ".globl " #name "\n.hidden " #name "\n" #name ":\n"
#define GUEST_FAULT_COPY_LOCAL(name) ".L" #name
#endif

extern "C" {
std::size_t GuestFaultCopyBytes(void* destination, const void* source, std::size_t bytes);
extern const char GuestFaultCopyAccess[];
extern const char GuestFaultCopyLoad[];
extern const char GuestFaultCopyStore[];
extern const char GuestFaultCopyWordLoad[];
extern const char GuestFaultCopyWordStore[];
extern const char GuestFaultCopyResume[];
}

__asm__(
#ifdef __APPLE__
    ".text\n"
    ".p2align 4\n"
    ".globl _GuestFaultCopyBytes\n"
    ".private_extern _GuestFaultCopyBytes\n"
    "_GuestFaultCopyBytes:\n"
#else
    ".pushsection .text\n"
    ".p2align 4\n"
    ".globl GuestFaultCopyBytes\n"
    ".hidden GuestFaultCopyBytes\n"
    ".type GuestFaultCopyBytes, @function\n"
    "GuestFaultCopyBytes:\n"
#endif
    ".cfi_startproc\n"
    "    movq %rdx, %rcx\n"
    "    cmpq $4, %rcx\n"
    "    ja " GUEST_FAULT_COPY_SYMBOL(GuestFaultCopyAccess) "\n"
    "    je " GUEST_FAULT_COPY_LOCAL(GuestFaultCopyWord) "\n"
    "    testq %rcx, %rcx\n"
    "    jz " GUEST_FAULT_COPY_SYMBOL(GuestFaultCopyResume) "\n"
    GUEST_FAULT_COPY_LABEL(GuestFaultCopyLoad)
    "    movb (%rsi), %al\n"
    GUEST_FAULT_COPY_LABEL(GuestFaultCopyStore)
    "    movb %al, (%rdi)\n"
    "    incq %rsi\n"
    "    incq %rdi\n"
    "    decq %rcx\n"
    "    jnz " GUEST_FAULT_COPY_SYMBOL(GuestFaultCopyLoad) "\n"
    "    jmp " GUEST_FAULT_COPY_SYMBOL(GuestFaultCopyResume) "\n"
    GUEST_FAULT_COPY_LOCAL(GuestFaultCopyWord) ":\n"
    "    movq %rsi, %rax\n"
    "    orq %rdi, %rax\n"
    "    testb $3, %al\n"
    "    jnz " GUEST_FAULT_COPY_SYMBOL(GuestFaultCopyLoad) "\n"
    GUEST_FAULT_COPY_LABEL(GuestFaultCopyWordLoad)
    "    movl (%rsi), %eax\n"
    GUEST_FAULT_COPY_LABEL(GuestFaultCopyWordStore)
    "    movl %eax, (%rdi)\n"
    "    xorq %rcx, %rcx\n"
    "    jmp " GUEST_FAULT_COPY_SYMBOL(GuestFaultCopyResume) "\n"
    GUEST_FAULT_COPY_LABEL(GuestFaultCopyAccess)
    "    rep movsb\n"
    GUEST_FAULT_COPY_LABEL(GuestFaultCopyResume)
    "    movq %rcx, %rax\n"
    "    ret\n"
    ".cfi_endproc\n"
#ifndef __APPLE__
    ".size GuestFaultCopyBytes, .-GuestFaultCopyBytes\n"
    ".popsection\n"
#endif
    );

namespace {

constexpr int CopySignals[] = {SIGSEGV, SIGBUS};
constexpr unsigned SegvSlot = 1u << 0;
constexpr unsigned AllSlots = (1u << std::size(CopySignals)) - 1;

struct sigaction g_previous[2][std::size(CopySignals)]{};
std::atomic<int> g_active{0};
std::atomic<std::uint64_t> g_installer{0};
std::atomic<unsigned> g_pending{0};
std::atomic<bool> g_ready{false};

bool SentByUser(const siginfo_t* info) {
#ifdef __APPLE__
    return info != nullptr && (info->si_code <= 0 || info->si_code >= SI_USER);
#else
    return info != nullptr && info->si_code <= 0;
#endif
}

std::uint64_t ThreadId() {
#ifdef __APPLE__
    std::uint64_t id = 0;
    pthread_threadid_np(nullptr, &id);
    return id;
#else
    return static_cast<std::uint64_t>(syscall(SYS_gettid));
#endif
}

void Chain(int signal, siginfo_t* info, void* context) {
    std::size_t slot = 0;
    while (slot < std::size(CopySignals) && CopySignals[slot] != signal) ++slot;
    if (slot == std::size(CopySignals)) return;
    const int active = g_active.load(std::memory_order_acquire);
    const struct sigaction previous = g_previous[active][slot];
    if (previous.sa_handler != SIG_DFL && previous.sa_handler != SIG_IGN) {
        if ((previous.sa_flags & SA_RESETHAND) != 0) {
            g_previous[active][slot] = {};
            g_previous[active][slot].sa_handler = SIG_DFL;
        }
        if ((previous.sa_flags & SA_SIGINFO) != 0 && previous.sa_sigaction != nullptr) {
            previous.sa_sigaction(signal, info, context);
            return;
        }
        previous.sa_handler(signal);
        return;
    }
    if (SentByUser(info) && previous.sa_handler == SIG_IGN) return;
    struct sigaction fallback{};
    fallback.sa_handler = SIG_DFL;
    sigemptyset(&fallback.sa_mask);
    sigaction(signal, &fallback, nullptr);
    if (SentByUser(info)) raise(signal);
}

void OnCopyFault(int signal, siginfo_t* info, void* context) {
    if (GuestFaultCopy::Resume(info, context)) return;
    Chain(signal, info, context);
}

bool InstallOwned(unsigned slots) {
    const int next = 1 - g_active.load(std::memory_order_relaxed);
    struct sigaction current[std::size(CopySignals)]{};
    bool ours = true;
    for (std::size_t slot = 0; slot < std::size(CopySignals); ++slot) {
        if ((slots & (1u << slot)) == 0) continue;
        if (sigaction(CopySignals[slot], nullptr, &current[slot]) != 0) return false;
        ours = ours && (current[slot].sa_flags & SA_SIGINFO) != 0 && current[slot].sa_sigaction == OnCopyFault;
    }
    if (ours) return true;
    for (std::size_t slot = 0; slot < std::size(CopySignals); ++slot) {
        const bool installed = (slots & (1u << slot)) == 0 || ((current[slot].sa_flags & SA_SIGINFO) != 0 && current[slot].sa_sigaction == OnCopyFault);
        g_previous[next][slot] = installed ? g_previous[1 - next][slot] : current[slot];
    }
    g_active.store(next, std::memory_order_release);
    for (std::size_t slot = 0; slot < std::size(CopySignals); ++slot) {
        if ((slots & (1u << slot)) == 0) continue;
        struct sigaction action{};
        action.sa_sigaction = OnCopyFault;
        action.sa_flags = SA_SIGINFO | SA_ONSTACK | SA_NODEFER | (g_previous[next][slot].sa_flags & SA_RESTART);
        action.sa_mask = g_previous[next][slot].sa_mask;
        if (sigaction(CopySignals[slot], &action, nullptr) != 0) return false;
    }
    return true;
}

bool Install(unsigned slots) {
    const auto self = ThreadId();
    for (std::uint64_t expected = 0; !g_installer.compare_exchange_weak(expected, self, std::memory_order_acquire); expected = 0) {
        if (expected == self) {
            g_pending.fetch_or(slots, std::memory_order_release);
            return true;
        }
    }
    bool installed = false;
    do {
        installed = InstallOwned(slots);
        slots = g_pending.exchange(0, std::memory_order_acquire);
    } while (installed && slots != 0);
    g_installer.store(0, std::memory_order_release);
    return installed;
}

bool Enabled() {
    return std::getenv("APS5_GUEST_COPY_SYSCALL") == nullptr;
}

}

namespace GuestFaultCopy {

bool Ready() {
    static const bool ready = [] {
        const bool installed = Enabled() && Install(AllSlots);
        g_ready.store(installed, std::memory_order_release);
        return installed;
    }();
    return ready;
}

void Reinstall() {
    if (g_ready.load(std::memory_order_acquire)) static_cast<void>(Install(SegvSlot));
}

bool Copy(void* destination, const void* source, std::size_t bytes) {
    return GuestFaultCopyBytes(destination, source, bytes) == 0;
}

bool Resume(const siginfo_t* info, void* context) {
    if (info == nullptr || context == nullptr || SentByUser(info)) return false;
    if (info->si_signo != SIGSEGV && info->si_signo != SIGBUS) return false;
#ifdef __APPLE__
    const auto state = static_cast<ucontext_t*>(context)->uc_mcontext;
    if (state == nullptr) return false;
    auto& rip = state->__ss.__rip;
#else
    auto& rip = static_cast<ucontext_t*>(context)->uc_mcontext.gregs[REG_RIP];
#endif
    const auto instruction = static_cast<std::uintptr_t>(rip);
    if (instruction != reinterpret_cast<std::uintptr_t>(GuestFaultCopyAccess) && instruction != reinterpret_cast<std::uintptr_t>(GuestFaultCopyLoad) && instruction != reinterpret_cast<std::uintptr_t>(GuestFaultCopyStore) && instruction != reinterpret_cast<std::uintptr_t>(GuestFaultCopyWordLoad) && instruction != reinterpret_cast<std::uintptr_t>(GuestFaultCopyWordStore)) return false;
    rip = static_cast<decltype(+rip)>(reinterpret_cast<std::uintptr_t>(GuestFaultCopyResume));
    return true;
}

}
#endif
