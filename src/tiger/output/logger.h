#ifndef TIGER_COMPILER_LOGGER_H
#define TIGER_COMPILER_LOGGER_H

#include <cstdarg>

#include "tiger/canon/canon.h"
#include "tiger/codegen/codegen.h"

class Logger {
public:
  explicit Logger(FILE *out = stdout) : out_(out) {}

  inline void Log(std::string_view msg, ...) const {
    va_list ap;
    va_start(ap, msg);
    vfprintf(out_, msg.data(), ap);
    va_end(ap);
  }
  inline void Log(cg::AssemInstr *instr_list, temp::Map *map) const {
    instr_list->Print(out_, map);
  }

private:
  FILE *out_;
};

class NullLogger {
public:
  constexpr NullLogger() noexcept = default;

  template <typename T, typename... Targs>
  inline void Log(T, Targs...) noexcept {}
};

#ifdef NDEBUG
#define TigerLog NullLogger().Log
#else
#define TigerLog Logger(stdout).Log
#endif

#endif // TIGER_COMPILER_LOGGER_H
