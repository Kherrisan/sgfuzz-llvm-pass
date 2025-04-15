#ifndef SGFUZZ_UTILS_H
#define SGFUZZ_UTILS_H

#include <cstdlib>

#define DEBUG_ENV "SGFUZZ_DEBUG"

static bool checkedEnv = false;
static const char *cachedEnv = nullptr;

inline const char *getCachedEnv(const char *varName)
{
    if (!checkedEnv)
    {
        cachedEnv = getenv(varName);
        checkedEnv = true;
    }
    return cachedEnv;
}

#define ENV_DEBUG(expr)                                \
    do                                                 \
    {                                                  \
        if (const char *env = getCachedEnv(DEBUG_ENV)) \
        {                                              \
            expr;                                      \
        }                                              \
    } while (0)

#endif