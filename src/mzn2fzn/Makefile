include ../../../Mercury.options.common

TARGET = mzn2fzn
TARGET_EXEC = $(addsuffix $(EXEEXT),$(TARGET))
TARGET_RC = $(addsuffix .realclean,$(TARGET))

EXT_DEPS = $(G12_MZN_FRONTEND_DIR)/*.m

.PHONY: all
all: install

.PHONY: default
default: install

.PHONY: check
check: install

$(TARGET_EXEC): Mercury.modules *.m minizinc_conf.m $(EXT_DEPS)
	$(G12_HOST_MMC) $(EXTRA_LINKAGE_FLAGS) --make $(TARGET)

Mercury.modules: *.m $(EXT_DEPS)
	$(G12_HOST_MMC) -f *.m $(EXT_DEPS)
	
.PHONY: install
install: $(TARGET_EXEC)
	mkdir -p $(G12_INSTALL_DIR)/bin
	$(INSTALL) $(TARGET_EXEC) $(G12_INSTALL_DIR)/bin

.PHONY: rebuild
rebuild:
	$(G12_HOST_MMC) --rebuild $(TARGET)

minizinc_conf.m: make_minizinc_conf
	./make_minizinc_conf $(G12_INSTALL_DIR) \
		"$(MZN_MAJOR_VERSION)" "$(MZN_MINOR_VERSION)" \
		"$(MZN_PATCH_VERSION)" $(ZINC_SEARCH_DIR_SEP_CHAR) \
		"$(shell date)" "$(OPTIMIZE)"

#----------------------------------------------------------------------------#

tags: *.m
	mtags $(wildcard *.m) $(wildcard $(G12_MZN_FRONTEND_DIR)/*.m)

.PHONY: distclean
distclean:
	$(G12_HOST_MMC) --make $(TARGET_RC)
	$(RM) -f Mercury.modules minizinc_conf.m tags
	$(RM) -rf Mercury
	$(RM) -f *.err *.mh

#----------------------------------------------------------------------------#
#----------------------------------------------------------------------------#

# For use by the packaging scripts.

.PHONY: unix_dist
unix_dist: minizinc_conf.m
	$(G12_HOST_MMC) --make $(TARGET_RC)
	$(RM) -f Mercury.modules
	$(G12_HOST_MMC) -f *.m $(G12_ZINC_FRONTEND_DIR)/*.m
	$(G12_HOST_MMC) $(MCFLAGS_FOR_STATIC_EXEC) --make $(TARGET)
	
.PHONY: mzn_dist
mzn_dist: Mercury.modules minizinc_conf.m
	$(G12_HOST_MMC) --make $(TARGET_RC)
	$(RM) -f Mercury.modules
	$(G12_HOST_MMC) -f *.m $(G12_ZINC_FRONTEND_DIR)/*.m
	$(G12_HOST_MMC) $(MCFLAGS_FOR_STATIC_EXEC) --make $(TARGET)

.PHONY: mzn_java
mzn_java: Mercury.modules minizinc_conf.m
	$(G12_HOST_MMC) --grade java --make  $(TARGET)

#----------------------------------------------------------------------------#
#----------------------------------------------------------------------------#
