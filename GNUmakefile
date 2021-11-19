AGDA_EXEC?=agda -W error -W noNoEquivWhenSplitting
FIX_WHITESPACE?=fix-whitespace
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
RUNHASKELL?=runhaskell
EVERYTHINGS=$(RUNHASKELL) ./Everythings.hs

.PHONY : all
all : check

.PHONY : test
test: check-whitespace gen-and-check-everythings check-README check

# checking and fixing whitespace

.PHONY : fix-whitespace
fix-whitespace:
	$(FIX_WHITESPACE)

.PHONY : check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

# checking and generating Everything files

.PHONY : check-everythings
check-everythings:
	$(EVERYTHINGS) check-except Experiments

.PHONY : gen-everythings
gen-everythings:
	$(EVERYTHINGS) gen-except Core Foundations Codata Experiments

.PHONY : gen-and-check-everythings
gen-and-check-everythings:
	$(EVERYTHINGS) gen-except Core Foundations Codata Experiments
	$(EVERYTHINGS) check Core Foundations Codata

.PHONY : check-README
check-README:
	$(EVERYTHINGS) check-README

# typechecking and generating listings for all files imported in README

.PHONY : check
check: gen-everythings
	$(AGDA) Cubical/README.agda
	$(AGDA) Cubical/WithK.agda

.PHONY : timings
timings: clean gen-everythings
	$(AGDA) -v profile.modules:10 Cubical/README.agda

.PHONY : listings
listings: $(wildcard Cubical/**/*.agda)
	$(AGDA) -i. -isrc --html Cubical/README.agda -v0

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete

