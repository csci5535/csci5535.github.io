.PHONY: render preview publish

render:
	quarto render

preview:
	quarto preview

publish:
	git commit -a && git push
