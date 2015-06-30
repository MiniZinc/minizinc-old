MMC = mmc

solns2out$(EXEEXT): Mercury.modules
	$(MMC) --make solns2out

Mercury.modules: *.m ../minizinc-frontend/*.m ../mzn2fzn/*.m
	$(MMC) -f $?

.PHONY: realclean
realclean:
	$(MMC) --make solns2out.realclean
	/bin/rm -rf Mercury
