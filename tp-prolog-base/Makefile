SWIPL=swipl

.PHONY: test
test:
	$(SWIPL) -g run_tests -t halt tests.pl --tty=true

.PHONY: repl
repl:
	$(SWIPL) nonograma.pl

.PHONY: watch
watch:
	sh -c "(make test; echo '')"
	fswatch -o *.pl | xargs -n1 -I{} sh -c "(make test; echo '')"
