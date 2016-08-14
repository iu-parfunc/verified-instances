HS = $(shell find src -type f -name '*.hs')
# Dummy target
CHS = $(subst hs,chs,$(HS))

all: check build

build:
	stack build

check: $(CHS)

%.chs: %.hs
	liquid -i src $<

clean:
	find . -type d -name '.liquid' -exec rm -rf {} \+
	stack clean

.PHONY: build check clean
