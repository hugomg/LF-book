.PHONY: all clean

all: $(patsubst %.nfa,%.dot.svg,$(wildcard *.nfa))

clean:
	rm -rf ./*.dot.svg

%.dot.svg: %.nfa
	awk -f gendot $< | dot -Tsvg -o $@

