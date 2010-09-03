OCB=ocamlbuild -use-ocamlfind -j 0

bin:
	$(OCB) main.native

byte:
	$(OCB) main.byte

test:
	$(OCB) -no-links test.native --

test.byte:
	$(OCB) -no-links test.native --

doc:
	$(OCB) project.docdir/index.html

view_doc:	doc
	xdg-open _build/project.docdir/index.html

dot:
	$(OCB) project.docdir/main.dot

view_dot:	dot
	dotty _build/project.docdir/main.dot &

all:	bin doc dot

clean:
	$(OCB) -clean

distclean:	clean
	rm -rf *~

archive:
	hg archive --type tbz2 ../fzip.tar.bz2
