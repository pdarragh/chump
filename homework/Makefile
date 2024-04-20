THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
ASSIGNMENTS   := $(filter-out . ./common,$(shell find . -maxdepth 1 -type d))
PDF_TARGETS   := $(patsubst %,%.pdf,$(ASSIGNMENTS))
SOURCE_EXTS   := md bib csl
SOURCE_FILES  := $(shell find ./common $(ASSIGNMENTS) -type f \( -iname $(shell echo $(SOURCE_EXTS:%=\\\*.%) | sed 's/ / -o -iname /g') \))
PANDOC        := pandoc --citeproc --resource-path common/

.PHONY: no-target all clean clean-all help $(ASSIGNMENTS)
.DEFAULT_GOAL: no-target

no-target:
	@echo make: Must specify a target!
	@exit 1

all: $(PDF_TARGETS)

clean:
	-$(RM) **/*.log **/*.tex

clean-all: clean
	-$(RM) $(PDF_TARGETS)

help:
	@echo "The following targets are supported:"
	@echo "    all                   make all the PDFs:"
	@echo "                            $(PDF_TARGETS)"
	@echo "    clean                 remove intermediate files"
	@echo "    clean-all             remove intermediate and result files"
	@echo "    <dir> OR <dir>.pdf    produce the PDF for the indicated directory,"
	@echo "                            where <dir> is one of:"
	@echo "                            $(ASSIGNMENTS)"

$(ASSIGNMENTS):
	@$(MAKE) -f $(THIS_MAKEFILE) $@.pdf

$(PDF_TARGETS): %.pdf: $(SOURCE_FILES)
	$(PANDOC) --resource-path "$*" -f markdown "$(sort $(filter ./$*/%.md,$(SOURCE_FILES)))" -o "$@"
	@echo "Built $@."
