//  file: Hello.java
//		This program should be in every folder for testing!
//			-- It illustrates the processing of the standard
//				command line arguments (ss, nn, mm).
//			-- Feel free to add to this program for your own testing.
// -- Chee (Basic Algorithms)

//import java.util.Arrays;

public class Hello {
	// METHODS======================:
	static void debug(String s){// helper method
		System.out.print(s);}
	static String tab (int n, char c){
		// returns a string of length n filled with c
		assert(n>0);
		char[] chars = new char[n];
		java.util.Arrays.fill(chars, c);
		return String.valueOf(chars); }//tab
	// MAIN=========================:
    public static void main (String[] argv){
		int ss = argv.length>0? Integer.valueOf(argv[0]) : 1111;
		int nn = argv.length>1? Integer.valueOf(argv[1]) : 100;
		int mm = argv.length>2? Integer.valueOf(argv[2]) : 10;
      System.out.println("Hello, world!");
	  debug("====================\n");
	  debug(" ss = " + String.valueOf(ss) +"\n");
	  debug(" nn = " + String.valueOf(nn) +"\n");
	  debug(" mm = " + String.valueOf(mm) +"\n");
	  debug(" ====================\n");

	  // EXTRA TESTS: =========================================
	  // If you type "make p=Hello r", it would have assertion failure
	  // If you type "make p=Hello r assert=", it NOT fail
	  tab(0,'-'); // assertion should fail!
	  ///
	  String s= tab(40, '-');
	  System.out.println("tab(40,-): "+s);
	  // padding
    }//main
}//class
