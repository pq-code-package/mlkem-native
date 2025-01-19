[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level mlkem-native in a single compilation unit

This directory contains a minimal example for how to build multiple instances of mlkem-native in a single compilation
unit. Only the C-backend is exercised.

The auto-generated source file [mlkem_native_monobuild.c](mlkem_native_monobuild.c) includes all mlkem-native C source
files. Moreover, it clears all `#define`s clauses set by mlkem-native at the end, and is hence amenable to multiple
inclusion in another compilation unit.

The manually written source file [mlkem_native_all.c](mlkem_native_all.c) includes
[mlkem_native_monobuild.c](mlkem_native_monobuild.c) three times, once for each of the three configuration files
[config_512.h](config_512.h), [config_768.h](config_768.h),
[config_1024.h](config_1024.h) for the different levels. For each inclusion, it sets `MLKEM_NATIVE_CONFIG_FILE`
appropriately first, and then includes the monobuild:
```C
/* Three instances of mlkem-native for all security levels */

/* Include level-independent code */
#define MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED
#define MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS

#define MLKEM_NATIVE_CONFIG_FILE "config_512.h"
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE

/* Exclude level-independent code */
#undef MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED
#define MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED

#define MLKEM_NATIVE_CONFIG_FILE "config_1024.h"
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE

#define MLKEM_NATIVE_CONFIG_FILE "config_768.h"
#undef MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE
```

Note the setting `MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED` which forces the inclusion of all level-independent
code in the MLKEM-512 build, and the setting `MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED`, which drops all
level-independent code in the subsequent builds. Finally, `MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS` entails that
`mlkem_native_monobuild.c` does not `#undefine` the `#define` clauses from level-independent files.

To make the monolithic multi-level build accessible from the application sources, we provide
[mlkem_native_all.h](mlkem_native_all.h), which includes [mlkem_native.h](../../mlkem/mlkem_native.h) once per
configuration. Note that we don't refer to the configuration using `MLKEM_NATIVE_CONFIG_FILE`, but by setting
`BUILD_INFO_XXX` explicitly. Otherwise, [mlkem_native.h](../../mlkem/mlkem_native.h) would include the confg, which
would lead to name-clashes upon multiple use.

```C
/* API for MLKEM-512 */
#define BUILD_INFO_LVL 512
#define BUILD_INFO_NAMESPACE(sym) mlkem512_##sym
#define BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef BUILD_INFO_LVL
#undef BUILD_INFO_NAMESPACE
#undef BUILD_INFO_NO_STANDARD_API
#undef MLKEM_NATIVE_H

/* API for MLKEM-768 */
#define BUILD_INFO_LVL 768
#define BUILD_INFO_NAMESPACE(sym) mlkem768_##sym
#define BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef BUILD_INFO_LVL
#undef BUILD_INFO_NAMESPACE
#undef BUILD_INFO_NO_STANDARD_API
#undef MLKEM_NATIVE_H

/* API for MLKEM-1024 */
#define BUILD_INFO_LVL 1024
#define BUILD_INFO_NAMESPACE(sym) mlkem1024_##sym
#define BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef BUILD_INFO_LVL
#undef BUILD_INFO_NAMESPACE
#undef BUILD_INFO_NO_STANDARD_API
#undef MLKEM_NATIVE_H
```

## Usage

Build this example with `make build`, run with `make run`.

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.
