all: pub talks tutorials

pub: ../bibtex/weirich.bib
	../tools/bib/makehtml

talks: ../cv/talks.md
	pandoc ../cv/talks.md -o pages/talks.html --css=../style.css

tutorials: ../cv/tutorials.md
	pandoc ../cv/tutorials.md -o pages/tutorials.html --css=../style.css