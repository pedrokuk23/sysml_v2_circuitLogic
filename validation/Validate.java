import org.omg.sysml.interactive.*;
import java.nio.file.*;
public class Validate {
  public static void main(String[] a) throws Exception {
    SysMLInteractive s = SysMLInteractive.getInstance();
    s.loadLibrary(a[0]);
    for (int i = 1; i < a.length; i++) {
      String src = new String(Files.readAllBytes(Paths.get(a[i])));
      SysMLInteractiveResult r = s.process(src);
      System.out.println("=== " + a[i]);
      System.out.println("syntax errors: " + r.getSyntaxErrors().size() + ", semantic errors: " + r.getSemanticErrors().size() + ", warnings: " + r.getWarnings().size());
      System.out.println(r.formatIssues());
      if (r.getException() != null) System.out.println(r.formatException());
    }
  }
}
