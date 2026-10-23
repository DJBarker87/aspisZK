// Diagnostic only: preserve exception propagation and print out_of_range stack.
#include <typeinfo>
#include <cstring>
#include <dlfcn.h>
#include <execinfo.h>
#include <unistd.h>
extern "C" [[noreturn]] void __cxa_throw(void *exception, std::type_info *info,
                                         void (*destroy)(void *)) {
  if (info && std::strstr(info->name(), "out_of_range")) {
    const char header[] = "S126 diagnostic out_of_range stack (not proof evidence):\n";
    write(2, header, sizeof(header)-1);
    void *frames[64];
    int count=backtrace(frames,64);
    backtrace_symbols_fd(frames,count,2);
  }
  using Throw=void (*)(void *,std::type_info *,void (*)(void *));
  auto original=reinterpret_cast<Throw>(dlsym(RTLD_NEXT,"__cxa_throw"));
  if (!original) _exit(98);
  original(exception,info,destroy);
  __builtin_unreachable();
}
