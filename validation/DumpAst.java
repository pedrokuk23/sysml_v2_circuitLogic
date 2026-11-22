import org.omg.sysml.interactive.*;
import org.omg.sysml.lang.sysml.*;
import org.eclipse.xtext.nodemodel.util.NodeModelUtils;
import org.eclipse.xtext.nodemodel.ICompositeNode;
import java.nio.file.*;
import java.util.*;

/** Dump the abstract syntax tree that the SysML v2 Pilot Implementation builds for a model, as JSON, so that the
 *  sysmlc front end can be cross-checked against it (tests/ast_check.py). One JSON object per owned element:
 *  metaclass, names, types, direction, and the facts each kind needs (operator, referent, literal text, relationship
 *  ends, transition source/target/guards, metadata). The interpretation is done on the Python side. */
public class DumpAst {
  static String q(String s) {
    if (s == null) return "null";
    StringBuilder b = new StringBuilder("\"");
    for (char c : s.toCharArray()) {
      if (c == '"' || c == '\\') b.append('\\').append(c);
      else if (c == '\n') b.append("\\n");
      else if (c < 32) b.append(' ');
      else b.append(c);
    }
    return b.append('"').toString();
  }
  static String text(Element e) {
    ICompositeNode n = NodeModelUtils.getNode(e);
    return n == null ? null : NodeModelUtils.getTokenText(n);
  }
  static String nm(Element e) { return e == null ? null : (e.getName() != null ? e.getName() : e.getShortName()); }
  static String list(Collection<? extends Element> l) {
    StringBuilder b = new StringBuilder("[");
    for (Element x : l) { if (b.length() > 1) b.append(','); b.append(q(x == null ? null : x.getQualifiedName())); }
    return b.append(']').toString();
  }

  static void dump(Element e, StringBuilder b, int depth) {
    if (depth > 60) return;
    b.append("{\"mc\":").append(q(e.eClass().getName()));
    b.append(",\"name\":").append(q(e.getDeclaredName()));
    b.append(",\"short\":").append(q(e.getDeclaredShortName()));
    b.append(",\"qn\":").append(q(e.getQualifiedName()));
    if (e instanceof Type) b.append(",\"conj\":").append(((Type) e).isConjugated());
    if (e instanceof Feature) {
      Feature f = (Feature) e;
      b.append(",\"types\":").append(list(f.getType()));
      b.append(",\"dir\":").append(q(f.getDirection() == null ? null : f.getDirection().getLiteral()));
      b.append(",\"end\":").append(f.isEnd());
      if (!f.getChainingFeature().isEmpty()) b.append(",\"chain\":").append(list(f.getChainingFeature()));
      List<Feature> rd = new ArrayList<>();
      for (Redefinition r : f.getOwnedRedefinition()) rd.add(r.getRedefinedFeature());
      if (!rd.isEmpty()) b.append(",\"redef\":").append(list(rd));
    }
    if (e instanceof Usage && ((Usage) e).isVariation()) b.append(",\"variation\":true");
    if (e instanceof Definition && ((Definition) e).isVariation()) b.append(",\"variation\":true");
    if (e instanceof OperatorExpression) b.append(",\"op\":").append(q(((OperatorExpression) e).getOperator()));
    if (e instanceof FeatureChainExpression) b.append(",\"target\":").append(q(((FeatureChainExpression) e).getTargetFeature().getQualifiedName()))
        .append(",\"targetName\":").append(q(nm(((FeatureChainExpression) e).getTargetFeature())));
    if (e instanceof FeatureReferenceExpression) {
      Feature r = ((FeatureReferenceExpression) e).getReferent();
      b.append(",\"ref\":").append(q(r == null ? null : r.getQualifiedName())).append(",\"refName\":").append(q(nm(r)));
      if (r != null) b.append(",\"refTypes\":").append(list(r.getType())).append(",\"refMc\":").append(q(r.eClass().getName()));
    }
    if (e instanceof Documentation) b.append(",\"body\":").append(q(((Documentation) e).getBody()));
    if (e instanceof LiteralExpression) b.append(",\"lit\":").append(q(text(e)));
    if (e instanceof Dependency) b.append(",\"client\":").append(list(((Dependency) e).getClient()))
        .append(",\"supplier\":").append(list(((Dependency) e).getSupplier()));
    if (e instanceof MetadataUsage) b.append(",\"meta\":").append(q(((MetadataUsage) e).getMetadataDefinition().getQualifiedName()));
    if (e instanceof TransitionUsage) {
      TransitionUsage t = (TransitionUsage) e;
      b.append(",\"src\":").append(q(nm(t.getSource()))).append(",\"dst\":").append(q(nm(t.getTarget())));
    }
    if (e instanceof Connector) {
      List<String> ends = new ArrayList<>();
      for (Feature f : ((Connector) e).getRelatedFeature()) {
        StringBuilder s = new StringBuilder();
        if (f != null && !f.getChainingFeature().isEmpty()) {
          for (Feature c : f.getChainingFeature()) { if (s.length() > 0) s.append('.'); s.append(nm(c)); }
        } else s.append(nm(f));
        ends.add(s.toString());
      }
      b.append(",\"ends\":[");
      for (int i = 0; i < ends.size(); i++) { if (i > 0) b.append(','); b.append(q(ends.get(i))); }
      b.append(']');
    }
    if (e instanceof SatisfyRequirementUsage) {
      SatisfyRequirementUsage s = (SatisfyRequirementUsage) e;
      b.append(",\"satisfied\":").append(q(nm(s.getSatisfiedRequirement()))).append(",\"by\":").append(q(nm(s.getSatisfyingFeature())));
    }
    b.append(",\"kids\":[");
    boolean first = true;
    for (Element k : e.getOwnedElement()) {
      if (k == null) continue;
      if (!first) b.append(',');
      first = false;
      dump(k, b, depth + 1);
    }
    // the result expression of a constraint body and the guard of a transition are owned through memberships
    b.append("]}");
  }

  public static void main(String[] a) throws Exception {
    SysMLInteractive s = SysMLInteractive.getInstance();
    s.loadLibrary(a[0]);
    String src = new String(Files.readAllBytes(Paths.get(a[1])));
    SysMLInteractiveResult r = s.process(src);
    if (r.hasErrors()) { System.err.println(r.formatIssues()); System.exit(1); }
    StringBuilder b = new StringBuilder();
    dump(r.getRootElement(), b, 0);
    Files.write(Paths.get(a[2]), b.toString().getBytes("UTF-8"));
  }
}
