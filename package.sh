rm Slugger.tar.gz
rm -rf Slugger
mkdir Slugger
cp -R ./{compile.sh,run.sh,package.sh,protein.txt,fastutil-8.2.3.jar,LICENSE,src,summary,Map,Makefile,README.txt,user_guide.pdf} ./Slugger
tar cvzf Slugger.tar.gz --exclude='._*' --exclude="*.iml" ./Slugger
rm -rf Slugger
echo done.
