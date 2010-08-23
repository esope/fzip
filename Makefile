OCB=ocamlbuild -j 0

bin:
	$(OCB) main.native

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
