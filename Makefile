HS = $(shell find src -type f -name '*.hs')
# Dummy target
CHS = $(subst hs,chs,$(HS))

DOCKER ?= true

ifeq ($(DOCKER),true)
	STACK ?= stack --docker
	ALL = docker build check
else
	STACK ?= stack
	ALL = build check
endif

LIQUID ?= $(STACK) exec liquid --

all: $(ALL)

docker:
	docker build -t liquidhaskell .

build:
	$(STACK) build

check: build $(CHS)

%.chs: %.hs
	$(LIQUID) -i src $<

clean:
	find . -type d -name '.liquid' -exec rm -rf {} \+
	$(STACK) clean

.PHONY: docker build check clean
