include ../../../Mercury.options.common

.PHONY: all
all: check

.PHONY: check
check:
	$(G12_HOST_MMC) --make g12_zinc_frontend.cs

tags: *.m
	mtags *.m

.PHONY: distclean
distclean:
	$(G12_HOST_MMC) --make g12_zinc_frontend.realclean
	$(RM) -rf Mercury
	$(RM) -f tags
