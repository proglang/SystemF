GOAL= main-tyde23
TARGET_MODULES= STLC Tagless-final
TARGET_FILES= agdamacros.tex unicodeletters.tex $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))
PREFIX= latex

ZIPFILES= README.md Makefile $(addsuffix .lagda, $(TARGET_MODULES)) Control/Concurrent/UntypedChannel.hs
ZIPGOAL= supplement-icfp23.zip

ARXIVGOAL= $(GOAL).zip

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES)
	pdflatex  --synctex=1 -interaction=nonstopmode $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<

$(ZIPGOAL): $(ZIPFILES)
	zip $@ $^

$(ARXIVGOAL): $(GOAL).tex $(GOAL).bbl $(TARGET_FILES) acmart.cls agda.sty ACM-Reference-Format.bst
	zip $@ $^

.PHONY: all type-check clean
all: $(GOAL).pdf $(ZIPGOAL)

### clean up

clean:
	$(RM) -f EX-multichannel
	$(RM) -rf MAlonzo
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done
