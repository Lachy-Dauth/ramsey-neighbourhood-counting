# make verify           - quick mode: every check that finishes in a few minutes (Python 3 + C/C++ compilers)
# make verify-full      - quick mode plus the long certificate checks and the direct clique searches (1.5-2 hours)
# make verify-controls  - the expensive negative and positive controls of the flag certificates (about 2 hours)
# make paper            - build the paper in paper/ (needs pdflatex)
# make clean            - remove build products and regenerated files
.PHONY: verify verify-full verify-controls paper clean
verify:
	sh ancillary/run_all.sh
verify-full:
	sh ancillary/run_all.sh --full
verify-controls:
	sh ancillary/run_all.sh --controls
paper:
	cd paper && for f in neighbourhood_counting; do pdflatex -interaction=nonstopmode $$f.tex >/dev/null && pdflatex -interaction=nonstopmode $$f.tex >/dev/null && echo "built paper/$$f.pdf"; done
clean:
	find ancillary -name __pycache__ -type d -prune -exec rm -rf {} +
	rm -f ancillary/clique_check ancillary/check_colouring_full ancillary/R_3_3_*_n*.txt
	rm -rf ancillary/extension_r3315/build
	rm -f paper/*.aux paper/*.log paper/*.out
