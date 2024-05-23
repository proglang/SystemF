GOAL= main-tyde24
SLIDES= slides-tyde23
TARGET_FILES= agdamacros.tex unicodeletters.tex ../src ../src/StratF/*.agda ../src/StratF/Util/*.agda ../src/StratF/Misc/*.agda STLC.lagda
PREFIX= latex

ZIPGOAL= supplement-tyde24.zip

ARXIVGOAL= $(GOAL).zip

AGDATEX= ../../agdatex/agdatex.py

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES) latex/STLC.tex
	$(AGDATEX) -v -r ../src ../src/StratF/*.agda ../src/StratF/Util/*.agda ../src/StratF/Misc/*.agda
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode $(GOAL)
	bibtex $(GOAL)
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<

supplement:
	rm -rf "__zip_cache"
	mkdir "__zip_cache"
	cp -r ../src/* "__zip_cache/"
	sed -i '/^ *--!/d' "__zip_cache"/**/*.agda # Remove agdatex comments
	gawk -i inplace 'BEGIN{RS="";ORS="\n\n"}1' "__zip_cache"/**/*.agda # Replace tripple newlines with double newlines.
	rm "__zip_cache/StratF/Misc/SubstExamples.agda"
	rm __zip_cache/**/*.agdai
	cd __zip_cache && zip -r ../$(ZIPGOAL) *
	rm -rf "__zip_cache/"

$(ARXIVGOAL): $(GOAL).tex $(GOAL).bbl $(TARGET_FILES) acmart.cls agda.sty ACM-Reference-Format.bst
	zip $@ $^

$(SLIDES).pdf: $(SLIDES).tex $(TARGET_FILES)
	pdflatex  --synctex=1 -interaction=nonstopmode $(SLIDES)

.PHONY: all type-check clean $(ZIPGOAL)

all: $(GOAL).pdf $(ZIPGOAL)

### agdatex

runagdatex:
	$(AGDATEX) -v -r ../src ../src/StratF/*.agda ../src/StratF/Util/*.agda ../src/StratF/Misc/*.agda

### clean up

clean:
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done