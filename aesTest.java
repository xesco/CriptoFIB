import java.math.BigInteger;
import java.util.Random;

public class aesTest {

    private static Random rand = new Random();
    private static int max = 64;
   
    public static void main(String args[]) {
        
        aes_cbc_test(128);
        aes_cbc_test(192);
        aes_cbc_test(256);
    }
   
    // tests aes using CBC mode and padded data (see aes.java 390)
    private static void aes_cbc_test(int Lk) {
        
        int incorrect=0;
        boolean error=false;
        for(int i=1; i<max; i++) {
            // Generate random bytes        
            System.out.println("Generating "+ i +" random bytes...");
            byte[] data = new byte[i];
            rand.nextBytes(data);
            // Generate random key
            System.out.println("Gererating random "+ Lk +" bits key...");
            byte[] key = new byte[Lk/8];
            rand.nextBytes(key);
            System.out.print("Plaintext bytes:");
            System.out.println(aes.getMessage(data));
            // Encrypt data
            byte[] C = aes.xifrarAES(data, new BigInteger(key) ,Lk);
            System.out.print("Ciphertext:");
            System.out.println(aes.getMessage(C));
            // Decrypt data
            byte[] M = aes.desxifrarAES(C, new BigInteger(key), Lk);
            System.out.print("Plaintext bytes:");
            System.out.println(aes.getMessage(M));
            // Check result
            for(int j=0; j<i && !error; j++) if(data[j] != M[j]) error = true;
            if(error) incorrect++;
            error=false;
            System.out.println("********************************");
        }
        // Print results
        System.out.println("Results:");
        System.out.println("Key length:  "+ Lk);
        System.out.println("Total tests: "+ max);
        System.out.println("Tests ok:    "+ (max-incorrect));
        System.out.println("Tests fail:  "+ incorrect);
    }
} 
