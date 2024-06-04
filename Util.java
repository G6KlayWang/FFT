//class Util 
//  These are useful tools for debugging, etc. 
//	Chee Yap, Basic Algorithm
import java.util.Random;

public class Util{
	// MEMBERS:
	//////////////////////////////////////////
		static int COUNT;
		static Random RG;
		static int verbosity=1; //0=silence. Larger number is more verbose
	// METHODS:
	//////////////////////////////////////////
	static void dbug(String ss){ //no \n
		if (verbosity>0) System.out.print(ss); } 
	static void debug(String ss){
		if (verbosity>0) System.out.println(ss); } 
	static void debug(String ss, String ff){
		// E.g., debug("Testing", "\n =========== %s:\n");
		if (verbosity>0) System.out.printf(ff, ss); } 
	static String tab (int n, char c){
		// returns a string of length n filled with c
		char[] chars = new char[n];
		java.util.Arrays.fill(chars, c);
		return String.valueOf(chars); }//tab
}
