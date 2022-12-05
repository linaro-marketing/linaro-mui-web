module.exports = (componentName) => ({
  content: `// Generated with util/create-component.js
  import React from "react";
  import { ${componentName}Props } from "./${componentName}.types";
  const ${componentName}: React.FC<${componentName}Props> = ({ foo }) => {
    return (
        <>
        </>
    )
  };
  export default ${componentName};
  `,
  extension: `.tsx`,
});
