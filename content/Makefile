all: pub talks tutorials cv

pub: ../bibtex/weirich.bib
	(cd ../tools/bib/; ./makehtml)

talks: ../cv/talks.md Makefile
	pandoc ../cv/talks.md -o talks.html --css=style.css

tutorials: ../cv/tutorials.md Makefile
	pandoc ../cv/tutorials.md -o tutorials.html --css=style.css

cv: ../cv/top.pdf
	(cd ../cv/; make)
	cp ../cv/top.pdf weirich-cv.pdf

export: pub talks tutorials cv
	rsync -av . sweirich@eniac.seas.upenn.edu:~/public_html