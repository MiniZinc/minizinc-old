MMC = mmc

minizinc$(EXEEXT): *.m
	$(MMC) --make minizinc

.PHONY: realclean
realclean:
	$(MMC) --make minizinc.realclean
	/bin/rm -rf Mercury
