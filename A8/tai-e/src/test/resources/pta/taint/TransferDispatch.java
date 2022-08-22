class TransferDispatch{
    public static void main(String[] args) {
        argToResult();
        baseToResult();
    }

    static void argToResult(){
        String taint = SourceSink.source();
        A b = new B();
        A c = new C();
        String s1 = b.a2r(taint);
        String s2 = c.a2r(taint);
        SourceSink.sink(s1); // taint
        SourceSink.sink(s2); // no taint
    }

    static void baseToResult(){
        String taint = SourceSink.source();
        A b = new B();
        A c = new C();
        b.getTaint(taint);
        c.getTaint(taint);
        SourceSink.sink(b.b2r()); // taint
        SourceSink.sink(c.b2r()); // no taint
    }
}

interface A{
    public String a2r(String a);
    public void getTaint(String a);
    public String b2r();
}

class B implements A{
    public String a2r(String a){
        return new String();
    }
    public void getTaint(String a){

    }
    public String b2r(){
        return new String();
    }
}

class C implements A{
    public String a2r(String a){
        return new String();
    }
    public void getTaint(String a){

    }
    public String b2r(){
        return new String();
    }
}