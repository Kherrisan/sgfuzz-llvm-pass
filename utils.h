#pragma once

#include <cstdlib>

#define DEBUG_ENV "SGFUZZ_DEBUG"

extern bool checkedEnv;
extern bool ENV_LOG_ENABLED;

#define ENV_DEBUG(expr)                                    \
    do                                                     \
    {                                                      \
        if (!checkedEnv)                                   \
        {                                                  \
            checkedEnv = true;                             \
            ENV_LOG_ENABLED = (getenv(DEBUG_ENV) != NULL); \
        }                                                  \
        if (ENV_LOG_ENABLED)                               \
        {                                                  \
            expr;                                          \
        }                                                  \
    } while (0)