AGDA_RTS ?= +RTS -A1g -RTS
AGDA ?= agda $(AGDA_RTS)

.PHONY: check html clean

# Typecheck every module of src/ in one Agda process.
check:
	@mkdir -p _build
	@(echo "module Everything where"; for f in $$(find src -name '*.agda' | sort); do \
	    echo "import $$(echo $${f#src/} | sed -E 's#/#.#g; s#\.agda$$##')"; done) > _build/Everything.agda
	$(AGDA) -i src -i _build _build/Everything.agda

# Typecheck and render every module to html/ (html/Everything.html lists them all).
html:
	@mkdir -p _build
	@(echo "module Everything where"; for f in $$(find src -name '*.agda' | sort); do \
	    echo "import $$(echo $${f#src/} | sed -E 's#/#.#g; s#\.agda$$##')"; done) > _build/Everything.agda
	$(AGDA) --html --html-dir=html -i src -i _build _build/Everything.agda

clean:
	find . -name '*.agdai' -delete
	rm -rf _build html
