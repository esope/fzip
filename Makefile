OCB=ocamlbuild -use-ocamlfind -j 0
DOTFILE=_project.dot

bin:
	$(OCB) main.byte

native:
	$(OCB) main.native

test:
	$(OCB) -no-links test.byte --

test.native:
	$(OCB) -no-links test.native --

doc:
	$(OCB) project.docdir/index.html

view_doc:	doc
	xdg-open project.docdir/index.html

dot:	ocamldot bin
	ocamldep -I _build _build/*.ml _build/*.mli | _build/tools/ocamldot/ocamldot.byte -fullgraph > _build/$(DOTFILE)

view_dot:	dot
	dot -T xlib _build/$(DOTFILE) &

all:	bin doc dot

clean:
	$(OCB) -clean

distclean:	clean
	rm -rf *~
	rm -rf examples/*/*~

archive:
	hg archive --type tbz2 ../fzip.tar.bz2

ocamldot:
	$(OCB) tools/ocamldot/ocamldot.byte
