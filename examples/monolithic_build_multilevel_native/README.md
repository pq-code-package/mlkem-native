[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level mlkem-native in a single compilation unit, with native code

This directory contains a minimal example for how to build multiple instances of mlkem-native in a single compilation
unit, while additionally linking assembly sources from native code.

The auto-generated source file [mlkem_native.c](mlkem_native/mlkem_native.c) includes all mlkem-native C source
files. Moreover, it clears all `#define`s clauses set by mlkem-native at the end, and is hence amenable to multiple
inclusion in another compilation unit.

The manually written source file [mlkem_native_all.c](mlkem_native_all.c) includes
[mlkem_native.c](mlkem_native/mlkem_native.c) three times, each time using the fixed config
[multilevel_config.h](multilevel_config.h), but changing the security level (specified
by `MLK_CONFIG_PARAMETER_SET`) every time. For each inclusion, it sets `MLK_CONFIG_FILE`
appropriately first, and then includes the monobuild:
```C
/* Three instances of mlkem-native for all security levels */

#define MLK_CONFIG_FILE "multilevel_config.h"

/* Include level-independent code */
#define MLK_CONFIG_MULTILEVEL_WITH_SHARED 1
/* Keep level-independent headers at the end of monobuild file */
#define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#define MLK_CONFIG_PARAMETER_SET 512
#include "mlkem_native.c"
#undef MLK_CONFIG_MULTILEVEL_WITH_SHARED
#undef MLK_CONFIG_PARAMETER_SET

/* Exclude level-independent code */
#define MLK_CONFIG_MULTILEVEL_NO_SHARED
#define MLK_CONFIG_PARAMETER_SET 768
#include "mlkem_native.c"
/* `#undef` all headers at the and of the monobuild file */
#undef MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#undef MLK_CONFIG_PARAMETER_SET

#define MLK_CONFIG_PARAMETER_SET 1024
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
```

Note the setting `MLK_CONFIG_MULTILEVEL_WITH_SHARED` which forces the inclusion of all level-independent
code in the MLKEM-512 build, and the setting `MLK_CONFIG_MULTILEVEL_NO_SHARED`, which drops all
level-independent code in the subsequent builds. Finally, `MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS` entails that
[mlkem_native.c](mlkem_native/mlkem_native.c) does not `#undefine` the `#define` clauses from level-independent files.

Since we embed [mlkem_native_all.c](mlkem_native_all.c) directly into the application source [main.c](main.c), we don't
need a header for function declarations. However, we still import [mlkem_native.h](../../mlkem/mlkem_native.h) once
with `MLK_CONFIG_CONSTANTS_ONLY`, for definitions of the sizes of the key material. Excerpt from [main.c](main.c):

```c
#include "mlkem_native_all.c"

#define MLK_CONFIG_CONSTANTS_ONLY
#include <mlkem_native.h>
```

## Usage

Build this example with `make build`, run with `make run`.

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.
