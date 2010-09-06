OCB=ocamlbuild -use-ocamlfind -j 0
DOTFILE=_project.dot

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

dot:	ocamldot bin
	ocamldep -I _build _build/*.ml _build/*.mli | _build/tools/ocamldot/ocamldot.native -fullgraph > _build/$(DOTFILE)

view_dot:	dot
	dot -T xlib _build/$(DOTFILE) &

all:	bin doc dot

clean:
	$(OCB) -clean

distclean:	clean
	rm -rf *~

archive:
	hg archive --type tbz2 ../fzip.tar.bz2

ocamldot:
	$(OCB) tools/ocamldot/ocamldot.native
