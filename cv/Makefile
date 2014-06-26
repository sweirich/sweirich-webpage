## if you add to these, you must update top.tex to refer to them as well
MD=cv funding students talks tutorials service university-service outreach teaching
PUBS=journal chapter conf thesis techreport

SOURCEBIB=../bibtex/weirich.bib
SOURCEMD=$(patsubst %,%.md,$(MD))

pdf: weirich-cv.pdf

bib: $(SOURCEBIB)
	mkdir -p temp
	bib2bib -s '$$date' -r -c '$$type = "ARTICLE"'  $(SOURCEBIB) > temp/journal.bib
	bib2bib -s '$$date' -r -c '$$type = "INCOLLECTION"'  $(SOURCEBIB) > temp/chapter.bib
	bib2bib -s '$$date' -r -c '$$type = "INPROCEEDINGS"' $(SOURCEBIB) > temp/conf.bib
	bib2bib -s '$$date' -r -c '$$type = "PHDTHESIS"' $(SOURCEBIB) > temp/thesis.bib
	bib2bib -s '$$date' -r -c '$$type = "TECHREPORT"' $(SOURCEBIB) > temp/techreport.bib

clean:
	rm -rf temp/
	rm *.bbl *.aux *.log *.blg *.out

# notes:
# + getting the unicode characters right requires xelatex --- pandoc just passes them through to the 
#   tex output

weirich-cv.pdf: bib
	mkdir -p temp
	for f in $(MD) ; do \
		pandoc $$f.md -o temp/$$f.tex -t latex ; \
	done
	xelatex top
	for f in $(PUBS); do \
	   bibtex $$f; \
	done
	xelatex top
	xelatex top
	echo $(SCOURCEMD)