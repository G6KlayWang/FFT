//  file: PolyMul.java
//		Example program for FFT algorithm
//		Maximum possible degree: 131072
//	These codes are written by Zhaoqi (TA for Chee Yap)
// -- Chee (Basic Algorithms)

import java.util.Random;

public class PolyMul extends Util {
	// METHODS======================:
	static void debug(String s){// helper method
		System.out.print(s+"\n");}
	static void debug(String s, int n){// helper method
		System.out.print(s + n+"\n");}
	static void debug(int n){// helper method
		System.out.print(n+"\n");}
	static void debug(String s, long n){// helper method
		System.out.print(s + n+"\n");}
	static void debug(long n){// helper method
		System.out.print(n+"\n");}
	static void debug(int[] a)
	{
		System.out.print("[");
		for(int i=0;i<a.length-1;++i)
			System.out.print(a[i]+",");
		System.out.print(a[a.length-1]+"]\n");
	}
	static void debug(long[] a)
	{
		System.out.print("[");
		for(int i=0;i<a.length-1;++i)
			System.out.print(a[i]+",");
		System.out.print(a[a.length-1]+"]\n");		
	}
	
	static long[] Euclid(long a,long b)
	{										// Extended Euclid’s Algorithm
		long[] s= {a,1,0};
		long[] t= {b,0,1};
		while((a%t[0])>0||(b%t[0])>0)
		{
			long[] r=new long[3];
			long q=s[0]/t[0];
			for(int i=0;i<3;++i)
				r[i]=s[i]-q*t[i];
			s=t;
			t=r;
		}
		return t;
	}
	
	static long inv(long w,long p)
	{										// find inverse of w in Z_p^*
		long[] t=Euclid(p,w);
		return (p+t[2]%p)%p;
	}

	// method for find the value in Zp
	static long fieldMod (long n, long p){
		long num = n % p;
		// in case the value is negative.
		if (num < 0) num += p;
		return num;
	}

	// method for calculating the power of omega in Zp
	static long powerofW(long start, long power, long p){
		long num = 1;
		// make sure the value in Zp
		start = fieldMod(start, p);
		for (int i = 0; i< power; i++){
			// make sure the value in Zp
			num = fieldMod(num*start, p);
		}

		return num;
	}

	static long[] FFT(long[] a,long w,long p)
	{										// a is the array of coefficients, length need to be 2^m
		if (a.length == 1) return a;		// w is the variable omega
											// p is the Z_p^*
		int n=a.length;
		long[] b=new long[n],c=new long[n/2],d=new long[n/2];

		// split the element on the odd and even index into two seperate arrays
		int Cindex = 0, Dindex = 0;
		for (int i = 0; i < a.length; i++){
			if (i % 2 == 0){
				c[Cindex++] = a[i];
			}
			else{
				d[Dindex++] = a[i];
			}
		}

		// do recursive FFT on the array of even and array of odd
		long [] even = FFT(c, fieldMod(w*w, p), p);
		long [] odd = FFT(d, fieldMod(w*w, p), p);

		// combine the even and odd array together by
		long power = 0; // power of omega starts at 0
		int combineIndex = 0; // corresponding position on the combined array
		for (int time = 0; time < 2; time++){
			for (int j = 0; j < n/2; j++){
				//even[i] + w**k*odd[i]
				long secondTerm = fieldMod(powerofW(w, power, p)* odd[j], p);
				b[combineIndex] =  fieldMod(even[j] + secondTerm, p);
				// incremenet the power of omega and the index of combined value
				power++;
				combineIndex++;
			}
		}
		return b;
	}
	
	static long[] prod(long[] f,long[] g,int n, long w,long p)
	{
		long[] ff=new long[n];
		long[] gg=new long[n];
		for(int i=0;i<n;++i)
		{									// Complete f and g
			if(i<f.length)
				ff[i]=(p+f[i]%p)%p;
			else
				ff[i]=0;
			if(i<g.length)
				gg[i]=(p+g[i]%p)%p;
			else
				gg[i]=0;
		}
		long[] f_value=FFT(ff,w,p);
		long[] g_value=FFT(gg,w,p);
		long[] fg_value=new long[n];
		for(int i=0;i<n;++i)
			fg_value[i]=(f_value[i]*g_value[i])%p;
		long[] fg=FFT(fg_value,inv(w,p),p);
		long inv_n=inv((long)n,p);
		for(int i=0;i<n;++i)
			fg[i]=(fg[i]*inv_n)%p;
		return fg;
	}
	
	static long[] p_list= {2,      3,      5,    17,      17,     97,    193,   257,
		     	 257,   7681,  12289, 12289,   12289,  40961,  65537, 65537,
		       65537, 786433, 786433};		// Which prime shall we choose to have an element with order 2^k.
	static long[] w_list= {1, 2,  2,  2, 3, 19, 11, 9, 3, 62, 49, 7, 41, 12, 15, 9,  3,  8, 5};
											// Which element in the Z_p^* that has order 2^k.
		
	static int getP(long n)
	{
		int k=(int)Math.ceil(Math.log(n)/Math.log(2));
		return (int)p_list[k];
	}
	
	static long[] prod(long[] f,long[] g)
	{										// Determine n,w,p.
		int m=f.length+g.length-1;						// Maximum possible degree.
		int k=(int)Math.ceil(Math.log(m)/Math.log(2));
		return prod(f,g,(int)Math.pow(2,k),w_list[k],p_list[k]);
	}
	
	static void showPoly(long[] h)
	{										// Output polynomial in the human written string.
		boolean first_term=true;
		for(int i=h.length-1;i>=0;--i)
		{
			if(h[i]==0)
				continue;
			else if(h[i]==1&&i==0)
				System.out.print("+1");
			else if(((h[i]>0&&first_term)||h[i]<0)&&h[i]!=1)
				System.out.print(h[i]);
			else if(h[i]>0&&h[i]!=1)
				System.out.print("+"+h[i]);
			else if(!first_term)
				System.out.print("+");
			else
				;
			first_term=false;
			if(i>1)
				System.out.print("x^"+i);
			else if(i==1)
				System.out.print("x");
		}
		System.out.print("\n");
	}

	// MAIN=========================:
    public static void main (String[] argv){
		int ss = argv.length>0? Integer.valueOf(argv[0]) : 11;			// random coefficients seed 11
		int nn = argv.length>1? Integer.valueOf(argv[1]) : 10;			// degree of polynomial 10
		int mm = argv.length>2? Integer.valueOf(argv[2]) : 1;			// maximum coefficient 1
		Random rgen = (ss==0)? new Random(): new Random(ss);
		switch(mm)
		{
		case 0:{
			/*

			long[] f={1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
			long[] g={0, 2, 0, 0, 3, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0};
			 */
			long[] f={16,1,0,16,1};
			long[] g={1,1,1,1};
			debug("Simple fixed polynomial multiplications;");
			debug("f(x)=x^4-x^3+x-1,");
			debug("g(x)=x^3+x^2+x+1,");
			debug("computing in Z_17:");
			showPoly(f);
			debug("*");
			showPoly(g);
			debug("=");
			showPoly(prod(f,g));
			break;
		}
		case 1:{
			long[] f=new long[nn+1];
			int P=getP(nn+1);
			for(int i=0;i<=nn;++i)
				f[i]=(long)rgen.nextInt(P);
			int k=(int)Math.ceil(Math.log(nn+1)/Math.log(2));
			int n=(int)Math.pow(2,k);
			long[] ff=new long[n];
			for(int i=0;i<n;++i)
				if(i<f.length)
					ff[i]=(P+f[i]%P)%P;
				else
					ff[i]=0;
			debug("FFT example for a random polynomial:");
			showPoly(ff);
			debug("p=",P);
			for(int i=0;i<1||i<nn/16;++i)
			{
				int w=rgen.nextInt(P-1)+1;
				debug("w=",w);
				debug(FFT(ff,w,P));
			}
			break;
		}
		case 2:{
			long[] f=new long[nn+1];
			long[] g=new long[nn+1];
			int P=getP(2*nn+1);
			for(int i=0;i<=nn;++i)
				f[i]=(long)rgen.nextInt(P);
			for(int i=0;i<=nn;++i)
				g[i]=(long)rgen.nextInt(P);
			debug("Polynomial multiplications for two random polynomials:");
			showPoly(f);
			debug("*");
			showPoly(g);
			debug("=");
			showPoly(prod(f,g));
			break;
		}
		default: return;
		}
    }//main
}//class
