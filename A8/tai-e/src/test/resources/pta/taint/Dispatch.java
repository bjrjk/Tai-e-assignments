class Dispatch{
    public static void main(String[] args) {
        A b = new B();
        A c = new C();
        SourceSink.sink(b.source()); // taint
        SourceSink.sink(c.source()); // no taint
    }
}

interface A{
    public String source();
}

class B implements A{
    public String source() {
        return new String();
    }
}

class C implements A{
    public String source() {
        return new String();
    }
}