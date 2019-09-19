all: pub talks tutorials 

pub: ../bibtex/weirich.bib
	(cd ../tools/bib/; ./makehtml)
	cp ../bibtex/weirich.bib .

talks: ../cv/talks.md Makefile
	pandoc ../cv/talks.md -o talks.html --css=style.css -s --metadata pagetitle="Talks"

tutorials: ../cv/tutorials.md Makefile
	pandoc ../cv/tutorials.md -o tutorials.html --css=style.css -s --metadata pagetitle="Tutorials"

cv: ../cv/top.pdf
	(cd ../cv/; make)
	cp ../cv/top.pdf weirich-cv.pdf

export: pub talks tutorials 
	rsync -av . sweirich@eniac.seas.upenn.edu:~/public_html
