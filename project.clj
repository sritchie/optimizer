
(defproject io.samritchie/optimizer "0.1.0-SNAPSHOT"
  :description "Boolean Optimizer in Clojure."
  :url "https://github.com/sritchie/optimizer"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/core.match "0.3.0-alpha4"]]
  :profiles {:provided
             {:dependencies [[org.clojure/clojure "1.6.0"]]}
             :dev
             {:dependencies [[org.clojure/test.check "0.7.0"]]}})
