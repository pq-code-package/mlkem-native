# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

.DEFAULT_GOAL := jedit
.PHONY: check-autocorrode check-afp setup-afp register-afp-components build pdf jedit \
	pipeline pipeline-flags pipeline-preprocess pipeline-theory pipeline-correctness

# Set this to the directory containing the Isabelle binary.
ISABELLE_HOME ?= /Applications/Isabelle2025-2.app/bin
# Root of the mlkem-native repository.
REPO_ROOT ?= $(abspath ../..)
# Set this to an AutoCorrode checkout.
AUTOCORRODE_DIR ?= $(REPO_ROOT)/AutoCorrode
# Set this to an AFP checkout containing Word_Lib and Isabelle_C
# (either flat or a full mirror-afp clone with thys/ subdirectory).
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

# Resolve AFP entry directory at shell level (handles ~ expansion and thys/ layout).
# Usage: $(call afp-entry-dir) expands AFP_COMPONENT_BASE in shell.
AFP_RESOLVE = base="$$(eval echo '$(AFP_COMPONENT_BASE)')"; \
	if [ -d "$$base/Word_Lib" ]; then echo "$$base"; \
	elif [ -d "$$base/thys/Word_Lib" ]; then echo "$$base/thys"; \
	else echo "$$base"; fi

ISABELLE_DIRS = \
	-d . \
	-d $(AUTOCORRODE_DIR) \
	-d $$($(AFP_RESOLVE))/Word_Lib \
	-d $$($(AFP_RESOLVE))/Isabelle_C

check-autocorrode:
	@if [ ! -f "$(AUTOCORRODE_DIR)/ROOT" ]; then \
		echo "Missing AutoCorrode checkout at $(AUTOCORRODE_DIR)."; \
		echo "Set AUTOCORRODE_DIR to your AutoCorrode checkout."; \
		exit 1; \
	fi

check-afp: check-autocorrode
	@afp_dir=$$($(AFP_RESOLVE)); \
	if [ ! -d "$$afp_dir/Word_Lib" ] || [ ! -d "$$afp_dir/Isabelle_C" ]; then \
		echo "Missing AFP entries at $(AFP_COMPONENT_BASE)."; \
		echo "Run 'make setup-afp' or set AFP_COMPONENT_BASE to an AFP checkout."; \
		exit 1; \
	fi

setup-afp:
	@afp_dir=$$($(AFP_RESOLVE)); \
	if [ -d "$$afp_dir/Word_Lib" ] && [ -d "$$afp_dir/Isabelle_C" ]; then \
		echo "AFP already available at $$afp_dir."; \
	else \
		base="$$(eval echo '$(AFP_COMPONENT_BASE)')"; \
		if [ -d "$$base" ] && [ ! -d "$$base/thys" ] && \
		   [ "$$(ls -A "$$base" 2>/dev/null)" != "" ]; then \
			echo "Directory $$base exists but does not contain Word_Lib or Isabelle_C."; \
			echo "Set AFP_COMPONENT_BASE to a valid AFP checkout."; \
			exit 1; \
		else \
			git clone --depth 1 https://github.com/isabelle-prover/mirror-afp-2025-1 "$$base"; \
		fi; \
	fi

register-afp-components: check-afp
	@afp_dir=$$($(AFP_RESOLVE)); \
	$(ISABELLE_HOME)/isabelle components -u "$$afp_dir/Word_Lib"; \
	$(ISABELLE_HOME)/isabelle components -u "$$afp_dir/Isabelle_C"

build: register-afp-components
	@afp_dir=$$($(AFP_RESOLVE)); \
	$(ISABELLE_HOME)/isabelle build $(ISABELLE_BUILD_FLAGS) \
	  -d . -d $(AUTOCORRODE_DIR) -d "$$afp_dir/Word_Lib" -d "$$afp_dir/Isabelle_C" \
	  $(ISABELLE_SESSION)

pdf: register-afp-components
	@afp_dir=$$($(AFP_RESOLVE)); \
	$(ISABELLE_HOME)/isabelle build $(ISABELLE_BUILD_FLAGS) \
	  -o document=pdf -o document_build=pdflatex \
	  -o "document_output=$(CURDIR)/output" \
	  -d . -d $(AUTOCORRODE_DIR) -d "$$afp_dir/Word_Lib" -d "$$afp_dir/Isabelle_C" \
	  $(ISABELLE_SESSION); \
	echo "PDF written to $(CURDIR)/output/"

jedit: register-afp-components
	@afp_dir=$$($(AFP_RESOLVE)); \
	$(ISABELLE_HOME)/isabelle jedit $(ISABELLE_JEDIT_FLAGS) -l HOL \
	  -d . -d $(AUTOCORRODE_DIR) -d "$$afp_dir/Word_Lib" -d "$$afp_dir/Isabelle_C" \
	  ./MLKEM_Functional_Correctness.thy &

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
