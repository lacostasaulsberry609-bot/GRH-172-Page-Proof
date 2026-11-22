.PHONY: pdf xelatex lualatex audit stats clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

xelatex:
	latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex

lualatex:
	latexmk -lualatex -interaction=nonstopmode -halt-on-error main.tex

audit:
	python3 ../tools/audit_300p.py

stats:
	python3 ../tools/audit_300p.py --stats

clean:
	latexmk -C
	rm -f chapters/*.aux
