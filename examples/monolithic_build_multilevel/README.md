[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level mlkem-native in a single compilation unit

This directory contains a minimal example for how to build multiple instances of mlkem-native in a single compilation
unit. Only the C-backend is exercised.

The auto-generated source file [mlkem_native_monobuild.c](mlkem_native_monobuild.c) includes all mlkem-native C source
files. Moreover, it clears all `#define`s clauses set by mlkem-native at the end, and is hence amenable to multiple
inclusion in another compilation unit.

The manually written source file [mlkem_native_all.c](mlkem_native_all.c) includes
[mlkem_native_monobuild.c](mlkem_native_monobuild.c) three times, each time using the fixed config
[multilevel_config.h](multilevel_config.h), but changing the security level (specified
by `MLK_CONFIG_PARAMETER_SET`) every time. For each inclusion, it sets `MLK_CONFIG_FILE`
appropriately first, and then includes the monobuild:
```C
/* Three instances of mlkem-native for all security levels */

/* Include level-independent code */
#define MLK_CONFIG_MULTILEVEL_WITH_SHARED
#define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS

#define MLK_CONFIG_PARAMETER_SET 512
#define MLK_CONFIG_FILE "multilevel_config.h"
#include "mlkem_native_monobuild.c"
#undef MLK_CONFIG_FILE

/* Exclude level-independent code */
#undef MLK_CONFIG_MULTILEVEL_WITH_SHARED
#define MLK_CONFIG_MULTILEVEL_NO_SHARED

#define MLK_CONFIG_PARAMETER_SET 768
#define MLK_CONFIG_FILE "multilevel_config.h"
#include "mlkem_native_monobuild.c"
#undef MLK_CONFIG_FILE

#undef MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS

#define MLK_CONFIG_PARAMETER_SET 1024
#define MLK_CONFIG_FILE "multilevel_config.h"
#include "mlkem_native_monobuild.c"
#undef MLK_CONFIG_FILE
```

Note the setting `MLK_CONFIG_MULTILEVEL_WITH_SHARED` which forces the inclusion of all level-independent
code in the MLKEM-512 build, and the setting `MLK_CONFIG_MULTILEVEL_NO_SHARED`, which drops all
level-independent code in the subsequent builds. Finally, `MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS` entails that
`mlkem_native_monobuild.c` does not `#undefine` the `#define` clauses from level-independent files.

To make the monolithic multi-level build accessible from the application sources, we provide
[mlkem_native_all.h](mlkem_native_all.h), which includes [mlkem_native.h](../../mlkem/mlkem_native.h) once per
configuration. Note that we don't refer to the configuration using `MLK_CONFIG_FILE`, but by setting
`MLK_BUILD_INFO_XXX` explicitly. Otherwise, [mlkem_native.h](../../mlkem/mlkem_native.h) would include the confg, which
would lead to name-clashes upon multiple use.

```C
/* API for MLKEM-512 */
#define MLK_BUILD_INFO_LVL 512
#define MLK_BUILD_INFO_NAMESPACE(sym) mlkem512_##sym
#define MLK_BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
#undef MLK_BUILD_INFO_NO_STANDARD_API
#undef MLK_H

/* API for MLKEM-768 */
#define MLK_BUILD_INFO_LVL 768
#define MLK_BUILD_INFO_NAMESPACE(sym) mlkem768_##sym
#define MLK_BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
#undef MLK_BUILD_INFO_NO_STANDARD_API
#undef MLK_H

/* API for MLKEM-1024 */
#define MLK_BUILD_INFO_LVL 1024
#define MLK_BUILD_INFO_NAMESPACE(sym) mlkem1024_##sym
#define MLK_BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
#undef MLK_BUILD_INFO_NO_STANDARD_API
#undef MLK_H
```

## Usage

Build this example with `make build`, run with `make run`.

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.
