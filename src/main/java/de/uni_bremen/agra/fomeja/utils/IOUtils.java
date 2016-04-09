package de.uni_bremen.agra.fomeja.utils;

import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;

/**
 * IOUtils provides functions to read and write from any kind of files.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public final class IOUtils {
	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private IOUtils() {}

	/**
	 * readFromFile reads the file at the given {@code URI} and returns its
	 *  content.
	 * 
	 * @param uri the {@code URI} to the file to read from
	 * @param encoding COMMENT
	 * 
	 * @return the content of the file at the given {@code URI}
	 * 
	 * @throws IOException if the file is not readable
	 */
	public static String readFromFile(String uri, String encoding) throws IOException {
		InputStream resourceStream = IOUtils.class.getResourceAsStream(uri);
		try {
			return readFromStream(resourceStream, encoding);
		} finally {
			resourceStream.close();
		}
	}

	/**
	 * readFromStream reads from the given stream and returns its content.
	 * 
	 * @param inputStream the input stream to read from
	 * @param encoding COMMENT
	 * 
	 * @return the content of the given input stream
	 * 
	 * @throws IOException if the stream is not readable
	 */
	public static String readFromStream(InputStream inputStream, String encoding) throws IOException {
		BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(inputStream, encoding));
		StringBuilder stringBuilder = new StringBuilder();
		String line = null;
		while ((line = bufferedReader.readLine()) != null) {
			stringBuilder.append(line);
			stringBuilder.append("\n");
		}
		bufferedReader.close();

		return stringBuilder.toString();
	}

	/**
	 * writeToFile writes the given text to the file at the given {@code URI}.
	 * 
	 * @param uri the {@code URI} to the file to write to
	 * @param text the text to write to the file at the given {@code URI}
	 * @param encoding COMMENT
	 * 
	 * @throws IOException COMMENT 
	 */
	public static void writeToFile(String uri, String text, String encoding) throws IOException {
		OutputStream outputStream = new FileOutputStream(uri);
		try {
			writeToStream(outputStream, text, encoding);
		} finally {
			outputStream.close();
		}
	}

	/**
	 * writeToStream writes the given text to the given output stream.
	 * 
	 * @param outputStream the output stream to write to
	 * @param text the text to write to the output stream
	 * @param encoding COMMENT
	 * 
	 * @throws UnsupportedEncodingException COMMENT
	 */
	public static void writeToStream(OutputStream outputStream, String text, String encoding) throws UnsupportedEncodingException {
		PrintWriter printWriter = new PrintWriter(new OutputStreamWriter(outputStream, encoding));
		printWriter.println(text);
		printWriter.flush();
		printWriter.close();
	}
}
