html: all
	rm -rf docs
	mkdir docs
	rocq doc --html --interpolate --parse-comments \
		--with-header extra/header.html --with-footer extra/footer.html \
		--toc \
		--coqlib_url https://rocq-prover.org/doc/V9.0.0/corelib \
    	--external https://rocq-prover.org/doc/V9.0.0/stdlib Stdlib \
		--external https://metarocq.github.io/html MetaRocq \
		-R theories ElmExtraction \
		-R tests/theories ElmExtraction.Tests \
		-d docs `find . -type f \( -wholename "*theories/*" -o -wholename "*test/*" \) -name "*.v" ! -wholename "./_opam/*"`
	cp extra/resources/coqdocjs/*.js docs
	cp extra/resources/coqdocjs/*.css docs
	cp extra/resources/toc/*.js docs
	cp extra/resources/toc/*.css docs
.PHONY: html
