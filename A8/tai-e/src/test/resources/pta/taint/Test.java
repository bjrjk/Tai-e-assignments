class Test {

    public static void main(String[] args) {
        String taint = SourceSink.source();
        String s = taint + "a";
        SourceSink.sink(s);
    }
}
