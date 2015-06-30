MMC = mmc

G12_INSTALL_DIR = /usr/local
MZN_MAJOR_VERSION = 1
MZN_MINOR_VERSION = 6
MZN_PATCH_VERSION = 0
ZINC_SEARCH_DIR_SEP_CHAR = ":"

OPTIMIZE = 

mzn2fzn$(EXEEXT): Mercury.modules *.m minizinc_conf.m
	$(MMC) --make mzn2fzn

Mercury.modules: *.m ../minizinc-frontend/*.m
	$(MMC) -f *.m ../minizinc-frontend/*.m
	
minizinc_conf.m: make_minizinc_conf
	./make_minizinc_conf $(G12_INSTALL_DIR) \
		"$(MZN_MAJOR_VERSION)" "$(MZN_MINOR_VERSION)" \
		"$(MZN_PATCH_VERSION)" $(ZINC_SEARCH_DIR_SEP_CHAR) \
		"$(shell date)" "$(OPTIMIZE)"

#----------------------------------------------------------------------------#

tags: *.m
	mtags *.m ../minizinc-frontend/*.m

.PHONY: realclean
realclean:
	$(MMC) --make mzn2fzn.realclean
	/bin/rm -f Mercury.modules minizinc_conf.m tags
	/bin/rm -rf Mercury
	/bin/rm -f *.err *.mh

#----------------------------------------------------------------------------#
#----------------------------------------------------------------------------#
