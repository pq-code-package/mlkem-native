[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level mlkem-native in a single compilation unit

This directory contains a minimal example for how to build multiple instances of mlkem-native in a single compilation
unit. Only the C-backend is exercised.

The auto-generated source file [mlkem_native.c](mlkem/mlkem_native.c) includes all mlkem-native C source
files. Moreover, it clears all `#define`s clauses set by mlkem-native at the end, and is hence amenable to multiple
inclusion in another compilation unit.

The manually written source file [mlkem_native_all.c](mlkem_native_all.c) includes
[mlkem_native.c](mlkem/mlkem_native.c) three times, each time using the fixed config
[multilevel_config.h](multilevel_config.h), but changing the security level (specified
by `MLK_CONFIG_PARAMETER_SET`) every time.
```C
#define MLK_CONFIG_FILE "multilevel_config.h"

/* Three instances of mlkem-native for all security levels */

/* Include level-independent code */
#define MLK_CONFIG_MULTILEVEL_WITH_SHARED
/* Keep level-independent headers at the end of monobuild file */
#define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#define MLK_CONFIG_PARAMETER_SET 512
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
#undef MLK_CONFIG_MULTILEVEL_WITH_SHARED

/* Exclude level-independent code */
#define MLK_CONFIG_MULTILEVEL_NO_SHARED
#define MLK_CONFIG_PARAMETER_SET 768
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
/* `#undef` all headers at the and of the monobuild file */
#undef MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS

#define MLK_CONFIG_PARAMETER_SET 1024
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
```

Note the setting `MLK_CONFIG_MULTILEVEL_WITH_SHARED` which forces the inclusion of all level-independent
code in the MLKEM-512 build, and the setting `MLK_CONFIG_MULTILEVEL_NO_SHARED`, which drops all
level-independent code in the subsequent builds. Finally, `MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS` entails that
`mlkem_native.c` does not `#undefine` the `#define` clauses from level-independent files.

To make the monolithic multi-level build accessible from the application source [main.c](main.c), we provide
[mlkem_native_all.h](mlkem_native_all.h), which includes [mlkem_native.h](../../mlkem/mlkem_native.h) once per
configuration. Note that we don't refer to the configuration using `MLK_CONFIG_FILE`, but by setting
`MLK_CONFIG_API_XXX` explicitly. Otherwise, [mlkem_native.h](../../mlkem/mlkem_native.h) would include the confg, which
would lead to name-clashes upon multiple use.

```C
#define MLK_CONFIG_API_NO_SUPERCOP

/* API for MLKEM-512 */
#define MLK_CONFIG_API_PARAMETER_SET 512
#define MLK_CONFIG_API_NAMESPACE_PREFIX mlkem512
#include <mlkem_native.h>
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_H

/* API for MLKEM-768 */
#define MLK_CONFIG_API_PARAMETER_SET 768
#define MLK_CONFIG_API_NAMESPACE_PREFIX mlkem768
#include <mlkem_native.h>
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_H

/* API for MLKEM-1024 */
#define MLK_CONFIG_API_PARAMETER_SET 1024
#define MLK_CONFIG_API_NAMESPACE_PREFIX mlkem1024
#include <mlkem_native.h>
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_H
```

## Usage

Build this example with `make build`, run with `make run`.

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.
