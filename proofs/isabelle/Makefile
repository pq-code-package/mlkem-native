# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

.DEFAULT_GOAL := jedit
.PHONY: check-autocorrode check-afp setup-afp register-afp-components build jedit \
	pipeline pipeline-flags pipeline-preprocess pipeline-theory pipeline-correctness

# Set this to the directory containing the Isabelle binary.
ISABELLE_HOME ?= /Applications/Isabelle2025-2.app/bin
# Root of the mlkem-native repository.
REPO_ROOT ?= $(abspath ../..)
# Set this to an AutoCorrode checkout.
AUTOCORRODE_DIR ?= $(REPO_ROOT)/AutoCorrode
# Set this to an AFP checkout containing Word_Lib and Isabelle_C.
AFP_COMPONENT_BASE ?= $(AUTOCORRODE_DIR)/dependencies/afp
# Main session provided by this directory.
ISABELLE_SESSION ?= MLKEM_Native_AutoCorrode

HOST := $(shell uname -s)
ifeq ($(HOST),Darwin)
	AVAILABLE_CORES ?= $(shell sysctl -n hw.physicalcpu)
else ifeq ($(HOST),Linux)
	AVAILABLE_CORES ?= $(shell nproc)
else
	$(error Unsupported host platform)
endif

# Build one session job using all available cores.
ISABELLE_BUILD_FLAGS ?= -b -j 1 -o "threads=$(AVAILABLE_CORES)" -v
ISABELLE_JEDIT_FLAGS ?=

ISABELLE_BUILD_FLAGS += $(ISABELLE_REMOTE)
ISABELLE_JEDIT_FLAGS += $(ISABELLE_REMOTE)

# Pipeline controls (proof translation units -> preprocessed C -> generated theories).
PIPELINE_SCRIPT ?= $(CURDIR)/pipeline/generate.py
PIPELINE_UNIT ?= poly
PIPELINE_PARAMETER_SET ?= 512
PIPELINE_OPT ?= 0
PIPELINE_AUTO ?= 0

ISABELLE_DIRS := \
	-d . \
	-d $(AUTOCORRODE_DIR) \
	-d $(AFP_COMPONENT_BASE)/Word_Lib \
	-d $(AFP_COMPONENT_BASE)/Isabelle_C

check-autocorrode:
	@if [ ! -f "$(AUTOCORRODE_DIR)/ROOT" ]; then \
		echo "Missing AutoCorrode checkout at $(AUTOCORRODE_DIR)."; \
		echo "Set AUTOCORRODE_DIR to your AutoCorrode checkout."; \
		exit 1; \
	fi

check-afp: check-autocorrode
	@if [ ! -d "$(AFP_COMPONENT_BASE)/Word_Lib" ] || [ ! -d "$(AFP_COMPONENT_BASE)/Isabelle_C" ]; then \
		echo "Missing AFP entries at $(AFP_COMPONENT_BASE)."; \
		echo "Run 'make setup-afp' or set AFP_COMPONENT_BASE to a mirror-afp-2025-1 checkout."; \
		exit 1; \
	fi

setup-afp:
	@if [ -d "$(AFP_COMPONENT_BASE)/Word_Lib" ] && [ -d "$(AFP_COMPONENT_BASE)/Isabelle_C" ]; then \
		echo "AFP already available at $(AFP_COMPONENT_BASE)."; \
	elif [ -d "$(AFP_COMPONENT_BASE)" ] && [ "$$(ls -A "$(AFP_COMPONENT_BASE)" 2>/dev/null)" != "" ]; then \
		echo "Directory $(AFP_COMPONENT_BASE) exists but does not look like mirror-afp-2025-1."; \
		echo "Please set AFP_COMPONENT_BASE to a valid AFP checkout."; \
		exit 1; \
	else \
		git clone --depth 1 https://github.com/isabelle-prover/mirror-afp-2025-1 "$(AFP_COMPONENT_BASE)"; \
	fi

register-afp-components: check-afp
	$(ISABELLE_HOME)/isabelle components -u $(AFP_COMPONENT_BASE)/Word_Lib
	$(ISABELLE_HOME)/isabelle components -u $(AFP_COMPONENT_BASE)/Isabelle_C

build: register-afp-components
	$(ISABELLE_HOME)/isabelle build $(ISABELLE_BUILD_FLAGS) $(ISABELLE_DIRS) $(ISABELLE_SESSION)

jedit: register-afp-components
	$(ISABELLE_HOME)/isabelle jedit $(ISABELLE_JEDIT_FLAGS) -l HOL $(ISABELLE_DIRS) ./MLKEM_Functional_Correctness.thy &

pipeline-flags:
	python3 $(PIPELINE_SCRIPT) --repo-root $(REPO_ROOT) --proof-root $(CURDIR) \
	  --unit $(PIPELINE_UNIT) --parameter-set $(PIPELINE_PARAMETER_SET) \
	  --opt $(PIPELINE_OPT) --auto $(PIPELINE_AUTO) --action flags

pipeline-preprocess:
	python3 $(PIPELINE_SCRIPT) --repo-root $(REPO_ROOT) --proof-root $(CURDIR) \
	  --unit $(PIPELINE_UNIT) --parameter-set $(PIPELINE_PARAMETER_SET) \
	  --opt $(PIPELINE_OPT) --auto $(PIPELINE_AUTO) --action preprocess

pipeline-theory:
	python3 $(PIPELINE_SCRIPT) --repo-root $(REPO_ROOT) --proof-root $(CURDIR) \
	  --unit $(PIPELINE_UNIT) --parameter-set $(PIPELINE_PARAMETER_SET) \
	  --opt $(PIPELINE_OPT) --auto $(PIPELINE_AUTO) --action theory

pipeline-correctness:
	python3 $(PIPELINE_SCRIPT) --repo-root $(REPO_ROOT) --proof-root $(CURDIR) \
	  --unit $(PIPELINE_UNIT) --parameter-set $(PIPELINE_PARAMETER_SET) \
	  --opt $(PIPELINE_OPT) --auto $(PIPELINE_AUTO) --action correctness

pipeline:
	python3 $(PIPELINE_SCRIPT) --repo-root $(REPO_ROOT) --proof-root $(CURDIR) \
	  --unit $(PIPELINE_UNIT) --parameter-set $(PIPELINE_PARAMETER_SET) \
	  --opt $(PIPELINE_OPT) --auto $(PIPELINE_AUTO) --action all
