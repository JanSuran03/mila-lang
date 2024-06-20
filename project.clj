(defproject mila-lang "0.1.0-SNAPSHOT"
  :dependencies [[cheshire "5.13.0"]
                 [org.clojure/clojure "1.12.0-beta1"]
                 [org.suskalo/coffi "0.6.409"]
                 [com.phronemophobic/clong "1.2"]
                 ;; only needed for parsing. not needed for generation
                 [org.bytedeco/llvm-platform "16.0.4-1.5.9"]]

  :repl-options {:init-ns mila-lang.core})
