HS = $(shell find src -type f -name '*.hs')
HS += examples/dpj/IntegerSumReduction2.hs examples/nbody/allpairs_verified.hs

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
	docker build -t parfunc/verified-instances:popl18 .

build:
	$(STACK) build

check: build $(CHS)

%.chs: %.hs
	$(LIQUID) -i src -i examples/nbody -i examples/dpj $<

clean:
	find . -type d -name '.liquid' -exec rm -rf {} \+
	$(STACK) clean

.PHONY: docker build check clean
