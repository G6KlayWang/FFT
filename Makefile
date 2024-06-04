# file: Makefile
#
#	You must NOT change this Makefile. 
#		It includes two files which you MAY change:
#		(1) make-include, used to set up your environment.
#			I provide a sample "make-include" to show 
#			how I customize my configuration, namely,
#				(Cygwin installed on a Windows 10 laptop).
#			You should customize it for own environment
#				(Mac, Linux, Windows).
#			If you are in Windows, then I suggest you install the Cygwin
#			to give you a Unix/Linux like operating system inside Windows.
#			Do internet search or talk to our Tutor for other OS.
#		(2) make-target, which is used for your own targets.
#			Again, see the sample "make-target" file.
#				E.g., we use targets like "t", "t1", "t9"... 
#					You must not use tXXX where XXX less than 100.
# 
#	HINTS:
#		-- This file is best viewed with an editor
#			that understands Makefile syntax and provides syntax colors
#		-- Note the following "standard" variables:
#
#				p:	name of program to run/compile
#				ss: seed for random generator (ss=0 is special)
#				nn: int value used by many programs
#				mm: int value if we need a second int 
#
#############################################
#	Prof. Chee Yap, Basic Algorithms
#############################################

# ================================================
# ENVIRONMENT CUSTOMIZATION:
# ================================================
# Put your customizations in a file called "make-include".
# 	To ensure that the default target is NOT over-ridden
#	by your make-include, we put the default here:
# FOR INSTRUCTORS: the make-include should change myName from "yap"
#	to "sol" when producing solutions.

default: compileAll

# the next include sets up the computing environment:
-include make-include

# program 
# ================================================
# Hello should be always available for small Java experiments
p=PolyMul
# standard command line arguments:
# ================================================
# the first 3 arguments for command lines are three integers:
ss=10
nn=10
mm=10
# Other arguments are optional:
a3=true
a4=abc
# We assemble them into a single argument:
args=$(ss) $(nn) $(mm) $(a3) $(a4) 

# hidden arguments:
_ss=$(ss)
_nn=$(nn)
_mm=$(mm)

# ================================================
# TARGETS
# ================================================
h help:
	-@echo "HELP:"
	-echo "    >make                  -- compile everything" 
	-@echo "    >make c               -- compile \$$(p)"
	-@echo "    >make r               -- run \$$(p)" 
	-@echo "    >make cr              -- compile and run \$$(p)" 
	-@echo "    >make test            -- this should match TESTOUTOUT
	-@echo "    >make t1 nn=12 ss=0   -- test1" 
	-@echo "    >make t2 mm=2 nn=321  -- test2 (etc)"

# default is to compile all *java programs
ca compileAll:
	test -d bin || mkdir bin
	$(javac) $(cflags) -d bin *.java 

# for doing only ONE program (great in debugging):
cr compileRun: c r

c compile javac compileOne:
	test -d bin || mkdir bin
	$(javac) $(cflags) -d bin $(p).java

r run java: 
	$(java) $(rflags) -classpath bin $(p) $(args)

r0 run0 java0: 
	$(java) $(rflags) -classpath bin $(p) 

# running a variant of $(p):
r1 run1 java1: 
	$(java) $(rflags) -classpath bin $(p)1 $(args) 

s showargs:
	@printf "ss= $(ss), nn=$(nn), mm=$(mm)\n"
	@printf "args= $(args)\n"

hello:
	@echo "Hello program is always available for testing!"
	$(java) -classpath bin Hello $(ss) $(nn)

hw currentHw :
	@echo "hw7 :"
	$(java) $(rflags) -classpath bin PolyMul 111 122 0

# ===> BE CAREFUL: this target will put its output into the file
#			myOUTPUT
#	If you have an original copy of this file, you might
#	want to save it under another name first!
t test:
	@echo "hw7, myOUTPUT :" 
	-rm myOUTPUT
	$(java) $(rflags) -classpath bin \
		PolyMul 111 64 0 \
		2>&1 | tee -a myOUTPUT

# ===> BE CAREFUL: this target will put its output into the file
#			myOUTPUT1
t1 test1:
	@echo "hw7, myOUTPUT1 :" 
	-rm myOUTPUT1
	$(java) $(rflags) -classpath bin \
		PolyMul 111 32 1 \
		2>&1 | tee -a myOUTPUT1

# ===> BE CAREFUL: this target will put its output into the file
#			myOUTPUT2
t2 test2:
	@echo "hw7, myOUTPUT2 :" 
	-rm myOUTPUT2
	$(java) $(rflags) -classpath bin \
		PolyMul 111 5 2 \
		2>&1 | tee -a myOUTPUT2

makeOutputs:
	make test
	make test1
	make test2

mvOutputs: 
	mv myOUTPUT TESTOUTPUT
	mv myOUTPUT1 TESTOUTPUT1
	mv myOUTPUT2 TESTOUTPUT2

t3 test3 myOUTPUT3:
	@echo "hw7, myOUTPUT3 :"
	$(java) $(rflags) -classpath bin PolyMul 111 200 2

t4 test4 myOUTPUT4:
	@echo "hw7, myOUTPUT4 :"
	$(java) $(rflags) -classpath bin PolyMul 111 100000 2

t9 test9 debug myOUTPUT9:
	@echo "hw7, myOUTPUT9 : (debugging)"
	$(java) $(rflags) -classpath bin PolyMul 1 $(_nn) 9

# The next include is for you to create your own targets:
#		REMEMBER: you must not interfere with our targets
#		E.g., do not have "t34" or "test34" as a target
#		because 34 is less than 100.  But you could have "t101".
-include make-target

# ================================================
# HOUSEKEEPING
# ================================================
e edit g gvim:
	$(gvim) $(p).java &

m makefile:
	$(gvim) Makefile &

clean:
	-rm -f bin/* .*~ *.class *~ src/*~  src/.*

v vclean: clean
	-rm -r bin

# Create zip file "hwXXX-YYY.zip" (e.g., "hw7-yap.zip") one level up:
zip:	vclean
	-test -f ../hw$(hwNumber)-$(myName).zip && \
			rm ../hw$(hwNumber)-$(myName).zip
	zip ../hw$(hwNumber)-$(myName).zip \
	 ../hw$(hwNumber)-$(myName)/PolyMul.java \
	 ../hw$(hwNumber)-$(myName)/Hello.java \
	 ../hw$(hwNumber)-$(myName)/Makefile \
	 ../hw$(hwNumber)-$(myName)/make-include \
	 ../hw$(hwNumber)-$(myName)/make-target \
	 ../hw$(hwNumber)-$(myName)/README \
	 ../hw$(hwNumber)-$(myName)/myOUTPUT \
	 ../hw$(hwNumber)-$(myName)/myOUTPUT1 \
	 ../hw$(hwNumber)-$(myName)/myOUTPUT2 \
	 ../hw$(hwNumber)-$(myName)/TESTOUTPUT \
	 ../hw$(hwNumber)-$(myName)/TESTOUTPUT1 \
	 ../hw$(hwNumber)-$(myName)/TESTOUTPUT2 \
	 ../hw7-yap.pdf \

# ================================================
# END
# ================================================
