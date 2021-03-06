# Copyright 2018 The Hafnium Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Select the project to build.
PROJECT ?= reference

# If HAFNIUM_HERMETIC_BUILD is "true" (not default), invoke `make` inside
# a container. The 'run_in_container.sh' script will set the variable value to
# 'inside' to avoid recursion.
ifeq ($(HAFNIUM_HERMETIC_BUILD),true)

# TODO: This is not ideal as (a) we invoke the container once per command-line
# target, and (b) we cannot pass `make` arguments to the script. We could
# consider creating a bash alias for `make` to invoke the script directly.

# Need to define at least one non-default target.
all:
	@$(CURDIR)/build/run_in_container.sh make PROJECT=$(PROJECT) $@

# Catch-all target.
.DEFAULT:
	@$(CURDIR)/build/run_in_container.sh make PROJECT=$(PROJECT) $@

else  # HAFNIUM_HERMETIC_BUILD

# Set path to prebuilts used in the build.
UNNAME_S := $(shell uname -s | tr '[:upper:]' '[:lower:]')
PREBUILTS := $(CURDIR)/prebuilts/$(UNNAME_S)-x64
GN ?= $(PREBUILTS)/gn/gn
NINJA ?= $(PREBUILTS)/ninja/ninja
export PATH := $(PREBUILTS)/clang/bin:$(PATH)


CHECKPATCH := $(CURDIR)/third_party/linux/scripts/checkpatch.pl \
	--ignore BRACES,SPDX_LICENSE_TAG,VOLATILE,SPLIT_STRING,AVOID_EXTERNS,USE_SPINLOCK_T,NEW_TYPEDEFS,INITIALISED_STATIC,FILE_PATH_CHANGES,EMBEDDED_FUNCTION_NAME,SINGLE_STATEMENT_DO_WHILE_MACRO,MACRO_WITH_FLOW_CONTROL --quiet

# Specifies the grep pattern for ignoring specific files in checkpatch.
# C++ headers, *.hh, are automatically excluded.
# Separate the different items in the list with a grep or (\|).
# debug_el1.c : uses XMACROS, which checkpatch doesn't understand.
# perfmon.c : uses XMACROS, which checkpatch doesn't understand.
# feature_id.c : uses XMACROS, which checkpatch doesn't understand.
CHECKPATCH_IGNORE := "src/arch/aarch64/hypervisor/debug_el1.c\|src/arch/aarch64/hypervisor/perfmon.c\|src/arch/aarch64/hypervisor/feature_id.c"

OUT ?= out/$(PROJECT)
OUT_DIR = out/$(PROJECT)

.PHONY: all
all: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)

$(OUT_DIR)/build.ninja:
	@$(GN) --export-compile-commands gen --args='project="$(PROJECT)"' $(OUT_DIR)

.PHONY: clean
clean:
	@$(NINJA) -C $(OUT_DIR) -t clean

.PHONY: clobber
clobber:
	rm -rf $(OUT)

# see .clang-format.
.PHONY: format
format:
	@echo "Formatting..."
	@find src/ -name \*.c -o -name \*.cc -o -name \*.h | xargs -r clang-format -style file -i
	@find inc/ -name \*.c -o -name \*.cc -o -name \*.h | xargs -r clang-format -style file -i
	@find test/ -name \*.c -o -name \*.cc -o -name \*.h | xargs -r clang-format -style file -i
	@find project/ -name \*.c -o -name \*.cc -o -name \*.h | xargs -r clang-format -style file -i
	@find . \( -name \*.gn -o -name \*.gni \) | xargs -n1 $(GN) format

.PHONY: checkpatch
checkpatch:
	@find src/ -name \*.c -o -name \*.h | grep -v $(CHECKPATCH_IGNORE) | xargs $(CHECKPATCH) -f
	@find inc/ -name \*.c -o -name \*.h | grep -v $(CHECKPATCH_IGNORE) | xargs $(CHECKPATCH) -f
	# TODO: enable for test/
	@find project/ -name \*.c -o -name \*.h | grep -v $(CHECKPATCH_IGNORE) | xargs $(CHECKPATCH) -f

# see .clang-tidy.
.PHONY: tidy
tidy: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)
	@echo "Tidying..."
	# TODO: enable readability-magic-numbers once there are fewer violations.
	# TODO: enable for c++ tests as it currently gives spurious errors.
	@find src/ \( -name \*.c \) | xargs clang-tidy -p $(OUT_DIR) -fix
	@find test/ \( -name \*.c \) | xargs clang-tidy -p $(OUT_DIR) -fix

.PHONY: check
check: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)
	@echo "Checking..."
	# TODO: enable for c++ tests as it currently gives spurious errors.
	@find src/ \( -name \*.c \) | xargs clang-check -p $(OUT_DIR) -analyze -fix-what-you-can
	@find test/ \( -name \*.c \) | xargs clang-check -p $(OUT_DIR) -analyze -fix-what-you-can

.PHONY: license
license:
	@find src/ -name \*.S -o -name \*.c -o -name \*.cc -o -name \*.h -o -name \*.dts | xargs -n1 python build/license.py --style c
	@find inc/ -name \*.S -o -name \*.c -o -name \*.cc -o -name \*.h -o -name \*.dts | xargs -n1 python build/license.py --style c
	@find test/ -name \*.S -o -name \*.c -o -name \*.cc -o -name \*.h -o -name \*.dts | xargs -n1 python build/license.py --style c
	@find build/ -name \*.py| xargs -n1 python build/license.py --style hash
	@find test/ -name \*.py| xargs -n1 python build/license.py --style hash
	@find . \( -name \*.gn -o -name \*.gni \) | xargs -n1 python build/license.py --style hash

.PHONY: update-prebuilts
update-prebuilts: prebuilts/linux-aarch64/linux/vmlinuz

prebuilts/linux-aarch64/linux/vmlinuz: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR) "third_party/linux"
	cp out/reference/obj/third_party/linux/linux.bin $@

endif  # HAFNIUM_HERMETIC_BUILD
