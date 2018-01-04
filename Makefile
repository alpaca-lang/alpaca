LOCAL_VERSION=alpaca-test
ALPACA=alpaca-${LOCAL_VERSION}

clean:
	rm -rf alpaca-${LOCAL_VERSION}
	rebar3 clean

compile:
	rebar3 compile
	VERSION=${LOCAL_VERSION} bash ./make-release.sh

eunit:
	ALPACA_ROOT=${ALPACA} rebar3 eunit

full_build: clean compile
	ALPACA_ROOT=${ALPACA} rebar3 compile
	ALPACA_ROOT=${ALPACA} rebar3 xref
	ALPACA_ROOT=${ALPACA} rebar3 eunit
	ALPACA_ROOT=${ALPACA} rebar3 ct
	ALPACA_ROOT=${ALPACA} rebar3 as default compile
