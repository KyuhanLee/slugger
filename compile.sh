echo Compiling Slugger...
rm -rf class
mkdir class

javac -cp ./fastutil-8.2.3.jar -d class $(find ./src -name *.java)

echo Make Slugger jar archive...
cd class
jar cf Slugger.jar ./
rm ../Slugger.jar
mv Slugger.jar ../
cd ..
rm -rf class
cd ..

echo Done.
