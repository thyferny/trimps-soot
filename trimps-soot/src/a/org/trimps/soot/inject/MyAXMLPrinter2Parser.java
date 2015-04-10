package a.org.trimps.soot.inject;

import java.io.BufferedInputStream;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import org.xmlpull.v1.XmlPullParserException;

import pxb.android.axml.AxmlVisitor;
import soot.jimple.infoflow.android.axml.AXmlAttribute;
import soot.jimple.infoflow.android.axml.AXmlNode;
import soot.jimple.infoflow.android.axml.parsers.AbstractBinaryXMLFileParser;
import android.content.res.AXmlResourceParser;

public class MyAXMLPrinter2Parser extends AbstractBinaryXMLFileParser {

	public void parseFile(String apkFilePath) throws Exception {
		// init
		AXmlNode node = null;
		AXmlNode parent = null;
		
		// create parser and parse the xml's contents
		JarFile jarFile = new JarFile(apkFilePath);
		Enumeration entries = jarFile.entries();
		while (entries.hasMoreElements()) {
			JarEntry je = (JarEntry) entries.nextElement();
			if (je.getName().equals("AndroidManifest.xml")) {
				AXmlResourceParser parser = new AXmlResourceParser();
				parser.open(jarFile.getInputStream(je));
				int type = -1;
				String tag;
				try {
					while ((type = parser.next()) != AXmlResourceParser.END_DOCUMENT) {
						switch (type) {
							// Currently nothing to do at the document's start
							case AXmlResourceParser.START_DOCUMENT:
								break;

							// To handle an opening tag we create a new node
							// and fetch the namespace and all attributes
							case AXmlResourceParser.START_TAG:
								tag = parser.getName();
								parent = node;
								node = new AXmlNode(tag, parser.getNamespace(), parent, false);
								this.addPointer(tag, node);
								
								// add attributes to node object
								for(int i = 0; i < parser.getAttributeCount(); i++) {
									String name = parser.getAttributeName(i);
									String ns = parser.getAttributeNamespace(i);
									AXmlAttribute<?> attr = null;
									
									// we only parse attribute of types string, boolean and integer
									switch(parser.getAttributeValueType(i)) {
										case AxmlVisitor.TYPE_STRING:
											attr = new AXmlAttribute<String>(name, parser.getAttributeValue(i), ns, false);
											break;
										case AxmlVisitor.TYPE_INT_BOOLEAN:
											attr = new AXmlAttribute<Boolean>(name, parser.getAttributeBooleanValue(i, false), ns, false);
											break;
										case AxmlVisitor.TYPE_FIRST_INT:
										case AxmlVisitor.TYPE_INT_HEX:
											attr = new AXmlAttribute<Integer>(name, parser.getAttributeIntValue(i, 0), ns, false);
											break;
									}
									
									// if we can't handle the attributes type we simply ignore it
									if(attr != null) node.addAttribute(attr);
								}
								break;
								
							// A closing tag indicates we must move
							// one level upwards in the xml tree
							case AXmlResourceParser.END_TAG:
								this.root = node;
								node = parent;
								parent = (parent == null ? null : parent.getParent());
								break;
								
							// Android XML documents do not contain text
							case AXmlResourceParser.TEXT:
								break;
							
							// Currently nothing to do at the document's end, see loop condition
							case AXmlResourceParser.END_DOCUMENT:
								break;
						}
					}
				} catch (XmlPullParserException ex) {
					throw new IOException(ex);
				}
				break;
			}
		}
	}

	@Override
	public void parseFile(byte[] buffer) throws IOException {
		
	}

}