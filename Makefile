HS = $(shell find src examples -type f -name '*.hs' \
	-not -path 'examples/dpj/*' -not -path 'examples/nbody/*')
# Dummy target
CHS = $(subst hs,chs,$(HS))

DOCKER ?= true
TIMEIT ?=

ifeq ($(DOCKER),true)
	STACK ?= stack --docker
	ALL = docker build check
else
	STACK ?= stack
	ALL = build check
endif

LIQUID ?= $(STACK) exec liquid --

ifeq ($(TIMEIT),true)
	LIQUID := time $(LIQUID) -q >/dev/null
endif

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
