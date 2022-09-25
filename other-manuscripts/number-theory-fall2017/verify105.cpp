/* verify105.cpp : The main runner program for the project; 
 * Author: Maxie D. Schmidt (maxieds@gmail.com) 
 * Created: 2018.10.04 
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <cmath>
#include <signal.h>
#include <time.h>
#include <sys/types.h>
#include <unistd.h>

#define MIN(x, y)         ((x < y) ? x : y)
#define MAX(x, y)         ((x < y) ? y : x)

#define MAX_BUFFER_LENGTH (256)
#define VERSIONSTR        ("VERIFY105 v0.1")


/**** : Some shorthands for space-saving storage types: ****/
typedef unsigned char uchar8; 
typedef unsigned short ushort16;
typedef unsigned int uint32;
typedef unsigned long int uint64;

/**** Constants and default parameter definitions: ****/
const uint64 initB1 = 5; 
uint64 fourTupleCaseCount = 0;
uint64 fourTupleCertCount = 0;
time_t runtimeStart = time(NULL); 

/**** Signal handlers for reporting status on-the-fly. 
      Note that this will drastically improve the running time by not having to 
      repeatedly print runtime status to the console. This status information can 
      instead be printed for the user on demand when they issue 
      "kill -1 PID" at the terminal (the PID is printed at the start of the program).
 ****/
void printStatusSignalHandler(int signum) { 
     fprintf(stderr, "\n=========================================================================\n\n"); 
     fprintf(stderr, "  => Currently running as PID %d\n", getpid());
     fprintf(stderr, "  => Total running time: % 3g hours OR % 3g days\n", 
             difftime(time(NULL), runtimeStart) / 3600.0, difftime(time(NULL), runtimeStart) / 3600.0 / 24.0); 
     fprintf(stderr, "  => Processed # 0x%016lx / %ld of cases so far\n", 
             fourTupleCaseCount, fourTupleCaseCount); 
     fprintf(stderr, "  => Processed ~ 2^{%g} OR ~ 3^{%g} 4-tuples\n", 
             log2(fourTupleCaseCount), log(fourTupleCaseCount) / log(3)); 
     fprintf(stderr, "  => Processed ~ 2^{%g} OR ~ 3^{%g} *ACTUAL CERTIFICATES*\n", 
             log2(fourTupleCertCount), log(fourTupleCertCount) / log(3)); 
 
     
     fprintf(stderr, "\n=========================================================================\n\n"); 
} 

/**** Define base and subclasses as wrappers around iterators for the 
      truncated digit expansions of the 4-tuple parameters. 
 ****/
template<int Base, int MaxDigit, int IntDigits, int FracDigits>
class TruncatedRealIter { 
     
     protected:
          int digitIndex[IntDigits + FracDigits + 1];
          int digitIndexSize;
          int lowerDigitPtr;
          int upperDigitPtr;
          bool iterDone;     

          inline void clearBefore(int stopIdx) { 
               for(int d = 0; d < stopIdx; d++) { 
                    digitIndex[d] = 0;
               } 
          }

     public:
          TruncatedRealIter() {
               digitIndexSize = IntDigits + FracDigits + 1;
               reset();
          }

          inline bool done() const {
               return iterDone;
          } 

          inline void reset() {
               for(int d = 0; d < digitIndexSize; d++) { 
                    digitIndex[d] = 0;
               } 
               lowerDigitPtr = upperDigitPtr = 0;
               iterDone = false;
          }

          inline bool next() { 
               if((upperDigitPtr + 1) == digitIndexSize && 
                  digitIndex[upperDigitPtr] == MaxDigit && 
                  (lowerDigitPtr + 1) == upperDigitPtr && 
                  digitIndex[lowerDigitPtr] == MaxDigit) { 
                    iterDone = true;
                    return false; 
               }
               else if(digitIndex[lowerDigitPtr] == MaxDigit && 
                       (lowerDigitPtr + 1) == upperDigitPtr) {
                    upperDigitPtr++;
                    digitIndex[upperDigitPtr]++;
		    clearBefore(upperDigitPtr);
                    lowerDigitPtr = 0;
               }
               else if(digitIndex[lowerDigitPtr] < MaxDigit) {
                    digitIndex[lowerDigitPtr]++;
               } 
               else if(digitIndex[lowerDigitPtr] == MaxDigit) { 
                    lowerDigitPtr++;
                    digitIndex[lowerDigitPtr]++;
               } 
               return true;
          } 

          inline double getReal() const { 
               double truncRealValue = 0.0;
               for(int i = 0; i <= IntDigits; i++) { 
                    truncRealValue += digitIndex[i] * pow(Base, i); 
               }
               for(int f = 1; f <= FracDigits; f++) { 
                    truncRealValue += digitIndex[f + MAX(0, IntDigits) - 1] * pow(Base, -1 * f); 
               } 
               return truncRealValue; 
          } 

          inline int getIntegerDigit(int pos) const { 
               if(pos < 0 || pos > IntDigits) { 
                    return -1;
               } 
               return digitIndex[pos];
          } 

          inline int getFractionalDigit(int pos) const { 
               if(pos < 1 || pos > FracDigits) { 
                    return -1;
               } 
               return digitIndex[IntDigits + pos];
          } 

};

typedef TruncatedRealIter<3,2,5,4> AlphaIter;
typedef TruncatedRealIter<3,2,5,3> GammaIter;
typedef TruncatedRealIter<5,4,-1,4> BetaIter;
typedef TruncatedRealIter<7,6,-1,3> DeltaIter;

/**** : Functions for producing (truncated) base-b expansions for 
        integers and fractions in [0, 1]: ****/ 
inline uchar8 * integer_base_b(ushort16 n, uchar8 base, int resize = true) { 
     if(base < 2) 
          return NULL;
     uchar8 rarr_size = (uchar8) ceil(log(n) / log(base));
     uchar8 *rarr = (uchar8 *) malloc(rarr_size * sizeof(uchar8));
     ushort16 q = n, k = 0;
     rarr[0] = rarr_size;
     while(q != 0) {
          rarr[++k] = q % base;
          q = q / base;
     }
     if(resize && k < rarr_size) {
          rarr = (uchar8 *) realloc(rarr, k * sizeof(uchar8));
          rarr[0] = rarr_size;
     }
     return rarr;
}

inline uchar8 * fractional_base_b(double f, uchar8 base, 
                                  int initpos, int endpos) { 
     if(base < 2 || f < 0.0 || f > 1.0) 
          return NULL;
     else if(initpos < 1 || endpos < initpos) 
          return NULL;
     uchar8 pos_shift_multiplier = (uchar8) pow(base, initpos - 1); 
     f *= pos_shift_multiplier;
     uchar8 rarr_size = endpos - initpos + 1;
     uchar8 *rarr = (uchar8 *) malloc(rarr_size * sizeof(uchar8));
     double modfi; 
     for(int bpos = initpos; bpos <= endpos; bpos++) { 
          f *= base;
          rarr[bpos - initpos] = (uchar8) modf(f, &modfi); 
     }
     return rarr;
}

inline bool check_integer_list(uchar8 *xilst, AlphaIter &ai, GammaIter &gi) {
     uint32 xilb_alpha = (int) ceil(log(ai.getReal()) / log(3)); 
     uint32 xilb_gamma = (int) ceil(log(gi.getReal()) / log(3));
     uint32 xilb = MAX(xilb_alpha, xilb_gamma); 
     for(int i = 1; i <= xilst[0]; i++) {
          if(xilst[i] <= xilb)
               return false;
     }
     return true;
}

inline double get_reciprocal3_sum(uchar8 *xilst) { 
     double recSum = 0.0;
     for(int i = 1; i <= xilst[0]; i++) { 
          recSum += pow(3, -1 * xilst[i]); 
     } 
     return recSum;
} 

/**** Main runner function: ****/
int main(int argc, char **argv) {

     signal(SIGHUP, printStatusSignalHandler); 
     fprintf(stdout, "NOW STARTING AS PID %d\n", getpid()); 

     uint64 currentB1 = initB1;
     uint64 lastUpdatedB1 = currentB1; 

     // Because our initial B1 is so small in this case, we can just 
     // enumerate a small list of all possibilities for the integer 
     // sets, \{x_i\}, all 2^{5}-1=31 of them, and keep them around without 
     // the need for recomputation until we are done. 
     // Notice that a significantly more advanced strategy involving 
     // hashing and dynamic programming would be required to handle 
     // larger cases of B1 >> 5. 
     uchar8 maxbin = (uchar8) (pow(2, currentB1) - 1);
     uchar8 xiarr[31][6] = {
	     {0x01, 0x01}, 
	     {0x01, 0x02}, 
	     {0x01, 0x03},
	     {0x01, 0x04},
	     {0x01, 0x05},
	     {0x02, 0x01, 0x02}, 
	     {0x02, 0x01, 0x03}, 
	     {0x02, 0x01, 0x04}, 
	     {0x02, 0x01, 0x05}, 
	     {0x02, 0x02, 0x03}, 
	     {0x02, 0x02, 0x04}, 
	     {0x02, 0x02, 0x05}, 
	     {0x02, 0x03, 0x04}, 
	     {0x02, 0x03, 0x05}, 
	     {0x02, 0x04, 0x05}, 
	     {0x03, 0x01, 0x02, 0x03}, 
	     {0x03, 0x01, 0x02, 0x04}, 
	     {0x03, 0x01, 0x02, 0x05}, 
	     {0x03, 0x01, 0x03, 0x04}, 
	     {0x03, 0x01, 0x03, 0x05}, 
	     {0x03, 0x01, 0x04, 0x05}, 
	     {0x03, 0x02, 0x03, 0x04}, 
	     {0x03, 0x02, 0x03, 0x05}, 
	     {0x03, 0x02, 0x04, 0x05}, 
	     {0x03, 0x03, 0x04, 0x05}, 
	     {0x04, 0x01, 0x02, 0x03, 0x04}, 
	     {0x04, 0x01, 0x02, 0x03, 0x05}, 
	     {0x04, 0x01, 0x02, 0x04, 0x05}, 
	     {0x04, 0x01, 0x03, 0x04, 0x05}, 
	     {0x04, 0x02, 0x03, 0x04, 0x05}, 
	     {0x05, 0x01, 0x02, 0x03, 0x04, 0x05} 
     };
     /*for(int x = 0; x < maxbin; x++) { 
          fprintf(stdout, "{ ");
	  for(int i = 1; i <= xiarr[x][0]; i++)
		  fprintf(stdout, "%d, ", xiarr[x][i]);
	  fprintf(stdout, "}\n"); 
     }*/

     // Now set up iterators (sequential access) to the distinct 
     // digit configurations of the 4-tuple search space:
     AlphaIter alphaIter;
     GammaIter gammaIter;
     BetaIter betaIter;
     DeltaIter deltaIter;

     // Finally, proceed with brute force to enumerate and exhaust all possibilities:)
     while(!alphaIter.done()) {
          
	  alphaIter.next(); 
	  if(alphaIter.getReal() > 43.0) {
		  ++fourTupleCaseCount;
		  continue;
	  }
          while(!gammaIter.done()) { 

	       gammaIter.next();
	       if(gammaIter.getReal() > 60.0) {
		    ++fourTupleCaseCount;
	            continue;
	       }
               while(!betaIter.done()) { 

		    betaIter.next();
                    while(!deltaIter.done()) { 

			 deltaIter.next();
                         if(alphaIter.getReal() / 3.0 + betaIter.getReal() > 1.0 || 
	                    gammaIter.getReal() / 3.0 + deltaIter.getReal() > 1.0) { 
				 ++fourTupleCaseCount;
				 continue;
			 }
			 
			 bool foundCert = false;
                         for(int xi = 0; xi < maxbin; xi++) { 

                              if(!check_integer_list(xiarr[xi], alphaIter, gammaIter)) { 
                                   continue;
                              }
                              bool digitTestPassed = true;
                              double testMod5 = alphaIter.getReal() * 
                                   get_reciprocal3_sum(xiarr[xi]) + betaIter.getReal();
                              if(testMod5 > 1.0)
                                   continue;
                              int t = xiarr[xi][0];  
                              int maxDigitU = MAX(1, (int) ceil(xiarr[xi][t] * log(3) / log(5))); 
                              uchar8 *digitsMod5 = fractional_base_b(testMod5, 5, 1, maxDigitU); 
                              //fprintf(stdout, "A=%g, B=%g, G=%g, D=%g\n", alphaIter.getReal(), 
			      //	      betaIter.getReal(), gammaIter.getReal(), deltaIter.getReal());
			      //fprintf(stdout, "  => XI = % 2d: ", xi);
			      //for(int d = 0; d < maxDigitU; d++) 
			      //      fprintf(stdout, "[%d]", digitsMod5[d]);
			      //fprintf(stdout, "\n");
			      for(int d = 0; d < maxDigitU; d++) { 
                                   if(digitsMod5[d] > 0x02) { 
                                        digitTestPassed = false;
                                        break;
                                   }
                              } 
                              free(digitsMod5);
                              if(!digitTestPassed) 
                                   continue; 
                              double testMod7 = gammaIter.getReal() * 
                                   get_reciprocal3_sum(xiarr[xi]) + deltaIter.getReal(); 
                              if(testMod7 > 1.0)
                                   continue;
                              int maxDigitV = MAX(1, (int) ceil(xiarr[xi][t] * log(3) / log(7))); 
                              uchar8 *digitsMod7 = fractional_base_b(testMod7, 7, 1, maxDigitV); 
                              //fprintf(stdout, "  => XI = % 2d: ", xi);
			      //for(int d = 0; d < maxDigitU; d++) 
			      //      fprintf(stdout, "[%d]", digitsMod5[d]);
			      //fprintf(stdout, "\n");

                              for(int d = 0; d < maxDigitV; d++) { 
                                   if(digitsMod7[d] > 0x03) { 
                                        digitTestPassed = false;
					break;
                                   } 
                              } 
                              free(digitsMod7); 
                              if(!digitTestPassed) 
                                   continue;
                              foundCert = true; 
                              ++fourTupleCertCount;
			      break; 
                         } // xi lists
                         if(!foundCert) { 
                              fprintf(stderr, "NO CERTIFICATE FOUND! [Case # 0x%016lx / %ld]\n", 
                                      fourTupleCaseCount, fourTupleCaseCount); 
                              fprintf(stderr, "  => Alpha ~ %g\n", alphaIter.getReal());
                              fprintf(stderr, "  => Gamma ~ %g\n", gammaIter.getReal());
                              fprintf(stderr, "  => Beta  ~ %g\n", betaIter.getReal());
                              fprintf(stderr, "  => Delta ~ %g\n", deltaIter.getReal());
                              fprintf(stderr, "TERMINATING AFTER % 3g HOURS ...\n", 
                                      difftime(time(NULL), runtimeStart) / 3600.0); 
                              return -1;
                         } 
                         ++fourTupleCaseCount; 
                    } // delta 
                    ++fourTupleCaseCount; 
               } // beta 
               ++fourTupleCaseCount; 
          } // gamma
          ++fourTupleCaseCount;
     } // alpha

     fprintf(stdout, "SUCCESSFULLY VERIFIED ALL CERTIFICATE CASES!\n"); 
     fprintf(stdout, "TOTAL RUNNING TIME: % 3g hours / % 3g days\n", difftime(time(NULL), runtimeStart) / 3600.0, 
             difftime(time(NULL), runtimeStart) / 3600.0 / 24.0); 

     return 0;
}

