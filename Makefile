all: compile demo
compile:
	-chmod u+x ./*.sh
	./compile.sh
demo:
	-chmod u+x ./*.sh
	@echo [DEMO] running SLUGGER
	./run.sh protein.txt true
	@echo [DEMO] summary graph is saved in the summary directory
